module

public import SerrinEpigraph.AnnularBranches

/-!
# Unions of compatible radial segments with a fixed inner radius
-/

public section
noncomputable section

open Set Filter
open scoped Topology Classical

namespace SerrinEpigraph

/-- Select a segment defined at the given radius; values outside the union are irrelevant. -/
@[expose] def annularUnion {ι : Type*} (a : ℝ) (R : ι → ℝ) (F : ι → ℝ → ℝ) (t : ℝ) : ℝ :=
  if h : ∃ i, t ∈ Ico a (R i) then F (Classical.choose h) t else 0

/-- The selected union agrees with each compatible segment on its half-open domain. -/
theorem annularUnion_eqOn {ι : Type*} {a : ℝ} {R : ι → ℝ} {F : ι → ℝ → ℝ}
    (hcompat : ∀ i j, EqOn (F i) (F j) (Icc a (min (R i) (R j)))) (i : ι) :
    EqOn (annularUnion a R F) (F i) (Ico a (R i)) := by
  intro t ht
  have he : ∃ j, t ∈ Ico a (R j) := ⟨i, ht⟩
  simp only [annularUnion, dite_eq_left he]
  exact hcompat (Classical.choose he) i
    ⟨ht.1, le_min (Classical.choose_spec he).2.le ht.2.le⟩

/-- On interior radii, the union locally agrees with any segment containing that radius. -/
theorem annularUnion_eventuallyEq {ι : Type*} {a : ℝ} {R : ι → ℝ} {F : ι → ℝ → ℝ}
    (hcompat : ∀ i j, EqOn (F i) (F j) (Icc a (min (R i) (R j))))
    {i : ι} {t : ℝ} (ht : t ∈ Ioo a (R i)) : annularUnion a R F =ᶠ[𝓝 t] F i := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact annularUnion_eqOn hcompat i ⟨hs.1.le, hs.2⟩

/-- The compatible union is continuous, including at its fixed inner endpoint. -/
theorem annularUnion_continuousOn {ι : Type*} {a : ℝ} {R : ι → ℝ} {F : ι → ℝ → ℝ}
    (hcompat : ∀ i j, EqOn (F i) (F j) (Icc a (min (R i) (R j))))
    (hF : ∀ i, ContinuousOn (F i) (Ico a (R i))) :
    ContinuousOn (annularUnion a R F) (⋃ i, Ico a (R i)) := by
  intro t ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  have hnear : Ico a (R i) ∈ 𝓝[⋃ j, Ico a (R j)] t := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hi.2)] with s hs hsR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hs
    exact ⟨hj.1, hsR⟩
  have hc := (hF i t hi).mono_of_mem_nhdsWithin hnear
  apply hc.congr_of_eventuallyEq _ (annularUnion_eqOn hcompat i hi)
  filter_upwards [hnear] with s hs
  exact annularUnion_eqOn hcompat i hs

/-- Both radial equations pass to a compatible union on its open domain. -/
theorem annularUnion_isRadialSystemOn {ι : Type*} {m : ℕ} {a : ℝ} {f : ℝ → ℝ}
    {R : ι → ℝ} {Q P : ι → ℝ → ℝ}
    (hQ : ∀ i j, EqOn (Q i) (Q j) (Icc a (min (R i) (R j))))
    (hP : ∀ i j, EqOn (P i) (P j) (Icc a (min (R i) (R j))))
    (hsys : ∀ i, IsRadialSystemOn m f (Q i) (P i) (Ioo a (R i))) :
    IsRadialSystemOn m f (annularUnion a R Q) (annularUnion a R P)
      (⋃ i, Ioo a (R i)) := by
  intro t ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  have heQ := annularUnion_eventuallyEq hQ hi
  have heP := annularUnion_eventuallyEq hP hi
  rw [heQ.eq_of_nhds, heP.eq_of_nhds]
  exact ⟨(hsys i t hi).1.congr_of_eventuallyEq heQ,
    (hsys i t hi).2.congr_of_eventuallyEq heP⟩

/-- Bounded radii make the half-open union terminate at their supremum. -/
theorem annularUnion_domain_eq_Ico {ι : Type*} [Nonempty ι] {a : ℝ} {R : ι → ℝ}
    (hR : BddAbove (range R)) : (⋃ i, Ico a (R i)) = Ico a (sSup (range R)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact ⟨hi.1, hi.2.trans_le (le_csSup hR (mem_range_self i))⟩
  · intro ht
    obtain ⟨r, ⟨i, rfl⟩, hi⟩ := exists_lt_of_lt_csSup (range_nonempty R) ht.2
    exact mem_iUnion.mpr ⟨i, ht.1, hi⟩

/-- The open union has the same supremal outer radius. -/
theorem annularUnion_domain_eq_Ioo {ι : Type*} [Nonempty ι] {a : ℝ} {R : ι → ℝ}
    (hR : BddAbove (range R)) : (⋃ i, Ioo a (R i)) = Ioo a (sSup (range R)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact ⟨hi.1, hi.2.trans_le (le_csSup hR (mem_range_self i))⟩
  · intro ht
    obtain ⟨r, ⟨i, rfl⟩, hi⟩ := exists_lt_of_lt_csSup (range_nonempty R) ht.2
    exact mem_iUnion.mpr ⟨i, ht.1, hi⟩

/-- All bounded extensions combine into a radial solution up to the supremal radius. -/
theorem IncreasingRadialSegment.exists_supremal_system
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (seed : IncreasingRadialSegment f m a b) (h : Hypotheses g u f κ)
    (hb : BddAbove (range (fun v : AnnularExtension seed ↦ v.radius))) :
    let S := sSup (range (fun v : AnnularExtension seed ↦ v.radius))
    ∃ Q P : ℝ → ℝ, ContinuousOn Q (Ico a S) ∧ ContinuousOn P (Ico a S) ∧
      IsRadialSystemOn m f Q P (Ioo a S) ∧
      EqOn Q seed.value (Ico a b) ∧ EqOn P seed.slope (Ico a b) ∧
      (∀ t ∈ Ico a S, Q t ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ P t) ∧
      (∀ t ∈ Ioo a S, 0 < Q t) := by
  let R := fun v : AnnularExtension seed ↦ v.radius
  let Q := fun v : AnnularExtension seed ↦ v.segment.value
  let P := fun v : AnnularExtension seed ↦ v.segment.slope
  have hQ := fun v w : AnnularExtension seed ↦ (v.compatible h w).1
  have hP := fun v w : AnnularExtension seed ↦ (v.compatible h w).2
  have hdom := annularUnion_domain_eq_Ico (a := a) hb
  have hdomi := annularUnion_domain_eq_Ioo (a := a) hb
  refine ⟨annularUnion a R Q, annularUnion a R P, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hdom]
    exact annularUnion_continuousOn hQ
      (fun v ↦ v.segment.value_continuous.mono Ico_subset_Icc_self)
  · rw [← hdom]
    exact annularUnion_continuousOn hP
      (fun v ↦ v.segment.slope_continuous.mono Ico_subset_Icc_self)
  · rw [← hdomi]
    exact annularUnion_isRadialSystemOn hQ hP
      (fun v t ht ↦ ⟨v.segment.value_derivative t ht, v.segment.slope_derivative t ht⟩)
  · exact annularUnion_eqOn hQ seed.selfExtension
  · exact annularUnion_eqOn hP seed.selfExtension
  · intro t ht
    rw [← hdom] at ht
    obtain ⟨v, hv⟩ := mem_iUnion.mp ht
    rw [annularUnion_eqOn hQ v hv, annularUnion_eqOn hP v hv]
    exact ⟨v.segment.value_range t ⟨hv.1, hv.2.le⟩,
      v.segment.slope_nonneg t ⟨hv.1, hv.2.le⟩⟩
  · intro t ht
    rw [← hdomi] at ht
    obtain ⟨v, hv⟩ := mem_iUnion.mp ht
    rw [annularUnion_eqOn hQ v ⟨hv.1.le, hv.2⟩]
    exact v.segment.value_pos t hv

end SerrinEpigraph
