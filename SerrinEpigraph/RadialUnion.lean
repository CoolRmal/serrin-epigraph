module

public import SerrinEpigraph.RadialZeroEndpoint

/-!
# Unions of compatible central radial profiles
-/

public section
noncomputable section
open Set
open scoped Topology Classical

namespace SerrinEpigraph

/-- Select any available branch at a nonnegative radius, with zero outside their union. -/
@[expose] def radialUnion {ι : Type*} (R : ι → ℝ) (F : ι → ℝ → ℝ) (t : ℝ) : ℝ :=
  if h : ∃ i, t ∈ Ico (0 : ℝ) (R i) then F (Classical.choose h) t else 0

/-- Compatibility makes the selected union equal to every branch on its domain. -/
theorem radialUnion_eqOn {ι : Type*} {R : ι → ℝ} {F : ι → ℝ → ℝ}
    (hcompat : ∀ i j, EqOn (F i) (F j) (Ico 0 (R i) ∩ Ico 0 (R j))) (i : ι) :
    EqOn (radialUnion R F) (F i) (Ico 0 (R i)) := by
  intro t ht
  have he : ∃ j, t ∈ Ico (0 : ℝ) (R j) := ⟨i, ht⟩
  simp only [radialUnion, dite_eq_left he]
  exact hcompat (Classical.choose he) i ⟨Classical.choose_spec he, ht⟩

/-- On positive interior radii, the union agrees locally with any available branch. -/
theorem radialUnion_eventuallyEq {ι : Type*} {R : ι → ℝ} {F : ι → ℝ → ℝ}
    (hcompat : ∀ i j, EqOn (F i) (F j) (Ico 0 (R i) ∩ Ico 0 (R j)))
    {i : ι} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (R i)) :
    radialUnion R F =ᶠ[𝓝 t] F i := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact radialUnion_eqOn hcompat i ⟨hs.1.le, hs.2⟩

/-- The union is continuous on its entire domain, including the center. -/
theorem radialUnion_continuousOn {ι : Type*} {R : ι → ℝ} {F : ι → ℝ → ℝ}
    (hcompat : ∀ i j, EqOn (F i) (F j) (Ico 0 (R i) ∩ Ico 0 (R j)))
    (hF : ∀ i, ContinuousOn (F i) (Ico 0 (R i))) :
    ContinuousOn (radialUnion R F) (⋃ i, Ico (0 : ℝ) (R i)) := by
  intro t ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  have hnear : Ico (0 : ℝ) (R i) ∈ 𝓝[⋃ j, Ico (0 : ℝ) (R j)] t := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hi.2)] with s hs hsR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hs
    exact ⟨hj.1, hsR⟩
  have hc := (hF i t hi).mono_of_mem_nhdsWithin hnear
  apply hc.congr_of_eventuallyEq _ (radialUnion_eqOn hcompat i hi)
  filter_upwards [hnear] with s hs
  exact radialUnion_eqOn hcompat i hs

/-- Compatible radial systems satisfy the same equations on the union of their positive domains. -/
theorem radialUnion_isRadialSystemOn {ι : Type*} {m : ℕ} {f : ℝ → ℝ}
    {R : ι → ℝ} {Q P : ι → ℝ → ℝ}
    (hQ : ∀ i j, EqOn (Q i) (Q j) (Ico 0 (R i) ∩ Ico 0 (R j)))
    (hP : ∀ i j, EqOn (P i) (P j) (Ico 0 (R i) ∩ Ico 0 (R j)))
    (hsys : ∀ i, IsRadialSystemOn m f (Q i) (P i) (Ioo 0 (R i))) :
    IsRadialSystemOn m f (radialUnion R Q) (radialUnion R P)
      (⋃ i, Ioo (0 : ℝ) (R i)) := by
  intro t ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  have heQ := radialUnion_eventuallyEq hQ hi
  have heP := radialUnion_eventuallyEq hP hi
  rw [heQ.eq_of_nhds, heP.eq_of_nhds]
  exact ⟨(hsys i t hi).1.congr_of_eventuallyEq heQ,
    (hsys i t hi).2.congr_of_eventuallyEq heP⟩

/-- The union preserves a common central value. -/
theorem radialUnion_center {ι : Type*} {R : ι → ℝ} {F : ι → ℝ → ℝ} {a : ℝ}
    (hcompat : ∀ i j, EqOn (F i) (F j) (Ico 0 (R i) ∩ Ico 0 (R j)))
    (i : ι) (hR : 0 < R i) (hF : F i 0 = a) : radialUnion R F 0 = a :=
  (radialUnion_eqOn hcompat i ⟨le_rfl, hR⟩).trans hF

/-- The union preserves normalized values wherever a branch is defined. -/
theorem radialUnion_mem_Ioo {ι : Type*} {R : ι → ℝ} {F : ι → ℝ → ℝ}
    (hcompat : ∀ i j, EqOn (F i) (F j) (Ico 0 (R i) ∩ Ico 0 (R j)))
    (hval : ∀ i t, t ∈ Ico (0 : ℝ) (R i) → F i t ∈ Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ ⋃ i, Ico (0 : ℝ) (R i)) : radialUnion R F t ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  rw [radialUnion_eqOn hcompat i hi]
  exact hval i t hi

/-- For bounded branch radii, the half-open union ends at their supremum. -/
theorem radialUnion_domain_eq_Ico {ι : Type*} [Nonempty ι] {R : ι → ℝ}
    (hR : BddAbove (range R)) :
    (⋃ i, Ico (0 : ℝ) (R i)) = Ico (0 : ℝ) (sSup (range R)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact ⟨hi.1, hi.2.trans_le (le_csSup hR (mem_range_self i))⟩
  · intro ht
    obtain ⟨r, ⟨i, rfl⟩, hi⟩ := exists_lt_of_lt_csSup (range_nonempty R) ht.2
    exact mem_iUnion.mpr ⟨i, ht.1, hi⟩

/-- The positive union likewise ends at the supremum of branch radii. -/
theorem radialUnion_positive_domain_eq_Ioo {ι : Type*} [Nonempty ι] {R : ι → ℝ}
    (hR : BddAbove (range R)) :
    (⋃ i, Ioo (0 : ℝ) (R i)) = Ioo (0 : ℝ) (sSup (range R)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact ⟨hi.1, hi.2.trans_le (le_csSup hR (mem_range_self i))⟩
  · intro ht
    obtain ⟨r, ⟨i, rfl⟩, hi⟩ := exists_lt_of_lt_csSup (range_nonempty R) ht.2
    exact mem_iUnion.mpr ⟨i, ht.1, hi⟩

end SerrinEpigraph
