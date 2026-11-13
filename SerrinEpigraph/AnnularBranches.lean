module

public import SerrinEpigraph.AnnularContinuation

/-!
# Compatible extensions of a fixed increasing radial segment
-/

public section

open Set

namespace SerrinEpigraph

/-- An increasing radial segment extending a fixed seed on its whole closed interval. -/
structure AnnularExtension {f : ℝ → ℝ} {m : ℕ} {a b : ℝ}
    (seed : IncreasingRadialSegment f m a b) where
  radius : ℝ
  segment : IncreasingRadialSegment f m a radius
  radius_ge : b ≤ radius
  value_eq : EqOn segment.value seed.value (Icc a b)
  slope_eq : EqOn segment.slope seed.slope (Icc a b)

/-- A seed supplies a member of its own extension family. -/
@[expose] def IncreasingRadialSegment.selfExtension {f : ℝ → ℝ} {m : ℕ} {a b : ℝ}
    (seed : IncreasingRadialSegment f m a b) : AnnularExtension seed where
  radius := b
  segment := seed
  radius_ge := le_rfl
  value_eq := fun _ _ ↦ rfl
  slope_eq := fun _ _ ↦ rfl

instance {f : ℝ → ℝ} {m : ℕ} {a b : ℝ} (seed : IncreasingRadialSegment f m a b) :
    Nonempty (AnnularExtension seed) := ⟨seed.selfExtension⟩

/-- Two extensions of a seed agree on the full closed intersection of their intervals. -/
theorem AnnularExtension.compatible
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (h : Hypotheses g u f κ) {seed : IncreasingRadialSegment f m a b}
    (v w : AnnularExtension seed) :
    EqOn v.segment.value w.segment.value (Icc a (min v.radius w.radius)) ∧
      EqOn v.segment.slope w.segment.slope (Icc a (min v.radius w.radius)) := by
  let S := Ioo a (min v.radius w.radius)
  have hab := seed.radii_lt
  have hmid : (a + b) / 2 ∈ S := by
    refine ⟨by linarith, lt_min ?_ ?_⟩ <;> linarith [v.radius_ge, w.radius_ge]
  have hseed : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hvS : S ⊆ Ioo a v.radius :=
    fun _ ht ↦ ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hwS : S ⊆ Ioo a w.radius :=
    fun _ ht ↦ ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
  obtain ⟨hQ, hP⟩ := h.radial_system_eqOn isOpen_Ioo
    (convex_Ioo a (min v.radius w.radius)).isPreconnected hmid
    (fun t ht ↦ ⟨seed.inner_pos.trans ht.1, v.segment.value_pos t (hvS ht)⟩)
    (fun t ht ↦ v.segment.value_derivative t (hvS ht))
    (fun t ht ↦ v.segment.slope_derivative t (hvS ht))
    (fun t ht ↦ w.segment.value_derivative t (hwS ht))
    (fun t ht ↦ w.segment.slope_derivative t (hwS ht))
    ((v.value_eq hseed).trans (w.value_eq hseed).symm)
    ((v.slope_eq hseed).trans (w.slope_eq hseed).symm)
  have hcl : closure S = Icc a (min v.radius w.radius) :=
    closure_Ioo (lt_min (hab.trans_le v.radius_ge) (hab.trans_le w.radius_ge)).ne
  have hvC : Icc a (min v.radius w.radius) ⊆ Icc a v.radius :=
    fun _ ht ↦ ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hwC : Icc a (min v.radius w.radius) ⊆ Icc a w.radius :=
    fun _ ht ↦ ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  constructor
  · exact hQ.of_subset_closure (v.segment.value_continuous.mono hvC)
      (w.segment.value_continuous.mono hwC) Ioo_subset_Icc_self (by rw [hcl])
  · exact hP.of_subset_closure (v.segment.slope_continuous.mono hvC)
      (w.segment.slope_continuous.mono hwC) Ioo_subset_Icc_self (by rw [hcl])

/-- The positive energy margin bounds every extension radius by the same finite number. -/
theorem IncreasingRadialSegment.extension_radii_bddAbove
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b δ : ℝ}
    (seed : IncreasingRadialSegment f m a b) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (hδ : 0 < δ)
    (hmargin : δ ^ 2 ≤ seed.slope a ^ 2 - 2 * normalizedPotential f 0 -
      2 * ((m : ℝ) / a * seed.slope a)) :
    BddAbove (range (fun v : AnnularExtension seed ↦ v.radius)) := by
  refine ⟨a + 1 / δ, ?_⟩
  rintro R ⟨v, rfl⟩
  have hs := v.slope_eq (show a ∈ Icc a b from ⟨le_rfl, seed.radii_lt.le⟩)
  have hm : δ ^ 2 ≤ v.segment.slope a ^ 2 - 2 * normalizedPotential f 0 -
      2 * ((m : ℝ) / a * v.segment.slope a) := by simpa only [hs] using hmargin
  have hw := v.segment.width_le hr h hδ hm
  linarith

/-- An extension attaining the supremal radius must reach value one. -/
theorem AnnularExtension.value_eq_one_of_radius_eq_sup
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b δ : ℝ}
    {seed : IncreasingRadialSegment f m a b} (v : AnnularExtension seed)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    (hmargin : δ ^ 2 ≤ seed.slope a ^ 2 - 2 * normalizedPotential f 0 -
      2 * ((m : ℝ) / a * seed.slope a))
    (hmax : v.radius = sSup (range (fun w : AnnularExtension seed ↦ w.radius))) :
    v.segment.value v.radius = 1 := by
  have hvle := (v.segment.value_range v.radius ⟨v.segment.radii_lt.le, le_rfl⟩).2
  by_contra hne
  have hvlt : v.segment.value v.radius < 1 := lt_of_le_of_ne hvle hne
  have hs := v.slope_eq (show a ∈ Icc a b from ⟨le_rfl, seed.radii_lt.le⟩)
  have hm : 0 < v.segment.slope a ^ 2 - 2 * normalizedPotential f 0 -
      2 * ((m : ℝ) / a * v.segment.slope a) := by
    rw [hs]
    exact (sq_pos_of_pos hδ).trans_le hmargin
  obtain ⟨d, hrd, w, hQ, hP⟩ := v.segment.exists_extension_of_energy_margin hr h hvlt hm
  let e : AnnularExtension seed := {
    radius := d
    segment := w
    radius_ge := v.radius_ge.trans hrd.le
    value_eq := fun x hx ↦ (hQ ⟨hx.1, hx.2.trans v.radius_ge⟩).trans (v.value_eq hx)
    slope_eq := fun x hx ↦ (hP ⟨hx.1, hx.2.trans v.radius_ge⟩).trans (v.slope_eq hx) }
  have hd := le_csSup (seed.extension_radii_bddAbove hr h hδ hmargin) (mem_range_self e)
  change d ≤ sSup (range (fun w : AnnularExtension seed ↦ w.radius)) at hd
  rw [← hmax] at hd
  linarith

end SerrinEpigraph
