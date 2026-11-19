module

public import SerrinEpigraph.ExcessBandWidth

/-!
# The phase and the perimeter outside the band (`GR10`, `GR11`, `GR13`)

* `volume_inter_measureTheoreticExterior`, `volume_measureTheoreticInterior_sdiff`,
  `disjoint_measureTheoreticInterior_exterior`: the open measure-theoretic interior and exterior
  are disjoint, and `E` is null on the exterior and conull on the interior.
* `subset_measureTheoreticInterior_or_exterior`: an open preconnected set without
  measure-theoretic boundary points lies in the interior or in the exterior.
* `IsPerimeterRepresentation.measure_compl_measureTheoreticBoundary`: the perimeter measure is
  carried by the measure-theoretic boundary.
* `SlabTrappedRepresentation.ae_abs_last_le`: for a slab-trapped representation, `μ`-a.e. point has
  height at most `H`.
* `SlabTrappedRepresentation.ae_mem_iff_of_band`: if all measure-theoretic boundary points over an
  open convex base lie in the band `|t - a| ≤ δ`, then above the band the phase is a.e. `E`, and
  below the band a.e. its complement (connectedness of the two components of the complement of the
  band, `GR13`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-! ### Measure-theoretic interior and exterior -/

theorem volume_inter_measureTheoreticExterior {d : ℕ} (E : Set (Space d)) :
    volume (E ∩ measureTheoreticExterior E) = 0 := by
  apply measure_null_of_locally_null
  rintro x ⟨-, r, hr, hnull⟩
  refine ⟨E ∩ ball x r, ?_, hnull⟩
  exact mem_nhdsWithin.mpr ⟨ball x r, isOpen_ball, mem_ball_self hr, fun z hz ↦ ⟨hz.2.1, hz.1⟩⟩

theorem volume_measureTheoreticInterior_sdiff {d : ℕ} (E : Set (Space d)) :
    volume (measureTheoreticInterior E \ E) = 0 := by
  apply measure_null_of_locally_null
  rintro x ⟨⟨r, hr, hnull⟩, -⟩
  refine ⟨ball x r \ E, ?_, hnull⟩
  exact mem_nhdsWithin.mpr ⟨ball x r, isOpen_ball, mem_ball_self hr, fun z hz ↦ ⟨hz.1, hz.2.2⟩⟩

theorem mem_interior_union_exterior_of_notMem_boundary {d : ℕ} {E : Set (Space d)}
    {x : Space d} (hx : x ∉ measureTheoreticBoundary E) :
    x ∈ measureTheoreticInterior E ∪ measureTheoreticExterior E := by
  by_contra hcon
  apply hx
  rw [← compl_measureTheoreticInterior_union_exterior]
  exact hcon

/-- An open preconnected set without measure-theoretic boundary points lies in the
measure-theoretic interior or in the measure-theoretic exterior. -/
theorem subset_measureTheoreticInterior_or_exterior {d : ℕ} {E V : Set (Space d)}
    (hV : IsPreconnected V) (hVb : ∀ x ∈ V, x ∉ measureTheoreticBoundary E) :
    V ⊆ measureTheoreticInterior E ∨ V ⊆ measureTheoreticExterior E :=
  hV.subset_or_subset (isOpen_measureTheoreticInterior E) (isOpen_measureTheoreticExterior E)
    (disjoint_measureTheoreticInterior_exterior E)
    (fun x hx ↦ mem_interior_union_exterior_of_notMem_boundary (hVb x hx))

/-! ### The perimeter measure is carried by the measure-theoretic boundary -/

theorem IsPerimeterRepresentation.measure_compl_measureTheoreticBoundary {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E W : Set (Space d)} {μ : Measure (Space d)}
    {ν : Space d → Space d} (h : IsPerimeterRepresentation b E W μ ν) (hW : IsOpen W) :
    μ (measureTheoreticBoundary E)ᶜ = 0 := by
  have hsplit : (measureTheoreticBoundary E)ᶜ ⊆ Wᶜ ∪ (W ∩ (measureTheoreticBoundary E)ᶜ) := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inr ⟨hxW, hx⟩
    · exact Or.inl hxW
  refine measure_mono_null hsplit (measure_union_null h.measure_compl ?_)
  apply measure_null_of_locally_null
  rintro x ⟨hxW, hxb⟩
  have hx' := mem_interior_union_exterior_of_notMem_boundary hxb
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW x hxW
  have key : ∃ r > 0, ball x r ⊆ W ∧ variationalPerimeter b E (ball x r) = 0 := by
    rcases hx' with ⟨r, hr, hnull⟩ | ⟨r, hr, hnull⟩
    · refine ⟨min r ε, lt_min hr hε, (ball_subset_ball (min_le_right _ _)).trans hεW, ?_⟩
      have hae : ∀ᵐ z ∂volume, z ∈ ball x (min r ε) → (z ∈ E ↔ z ∈ (univ : Set (Space d))) := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz hzb
        simp only [mem_univ, iff_true]
        by_contra hzE
        exact hz ⟨ball_subset_ball (min_le_left _ _) hzb, hzE⟩
      rw [variationalPerimeter_congr_ae_on b hae, variationalPerimeter_univ]
    · refine ⟨min r ε, lt_min hr hε, (ball_subset_ball (min_le_right _ _)).trans hεW, ?_⟩
      have hae : ∀ᵐ z ∂volume, z ∈ ball x (min r ε) → (z ∈ E ↔ z ∈ (∅ : Set (Space d))) := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz hzb
        simp only [mem_empty_iff_false, iff_false]
        intro hzE
        exact hz ⟨hzE, ball_subset_ball (min_le_left _ _) hzb⟩
      rw [variationalPerimeter_congr_ae_on b hae, variationalPerimeter_empty]
  obtain ⟨r, hr, hrW, hP⟩ := key
  refine ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr), ?_⟩
  rw [h.measure_open _ isOpen_ball hrW, hP]

theorem IsPerimeterRepresentation.ae_mem_measureTheoreticBoundary {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E W : Set (Space d)} {μ : Measure (Space d)}
    {ν : Space d → Space d} (h : IsPerimeterRepresentation b E W μ ν) (hW : IsOpen W) :
    ∀ᵐ x ∂μ, x ∈ measureTheoreticBoundary E ∧ x ∈ W := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (h.measure_compl_measureTheoreticBoundary hW),
    measure_eq_zero_iff_ae_notMem.mp h.measure_compl] with x h1 h2
  exact ⟨by simpa using h1, by simpa using h2⟩

/-! ### Convex bands over a convex base -/

theorem convex_cylinder_Ioo {m : ℕ} {B : Set (Space m)} (hB : Convex ℝ B) (lo hi : ℝ) :
    Convex ℝ {x : Space (m + 1) | horizontal x ∈ B ∧ x (Fin.last m) ∈ Ioo lo hi} := by
  have h1 : Convex ℝ (horizontalContinuousLinearMap.toLinearMap ⁻¹' B) :=
    hB.linear_preimage _
  have h2 : Convex ℝ
      ((EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).toLinearMap ⁻¹' Ioo lo hi) :=
    (convex_Ioo lo hi).linear_preimage _
  exact h1.inter h2

theorem isOpen_cylinder_Ioo {m : ℕ} {B : Set (Space m)} (hB : IsOpen B) (lo hi : ℝ) :
    IsOpen {x : Space (m + 1) | horizontal x ∈ B ∧ x (Fin.last m) ∈ Ioo lo hi} :=
  (hB.preimage continuous_horizontal).inter
    (isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous)

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- `μ`-almost every point is a measure-theoretic boundary point in the cylinder, hence lies in
the trapping slab `|t| ≤ H`. -/
theorem ae_abs_last_le (hS : SlabTrappedRepresentation b E U H H' μ ν) :
    ∀ᵐ x ∂μ, x ∈ measureTheoreticBoundary E ∧ x ∈ cylinderSet U H' ∧
      |x (Fin.last m)| ≤ H := by
  filter_upwards [hS.rep.ae_mem_measureTheoreticBoundary (isOpen_cylinderSet hS.isOpen H')]
    with x hx
  refine ⟨hx.1, hx.2, hS.abs_last_le_of_mem_measureTheoreticBoundary hx.1 hx.2.1
    (abs_lt.mpr hx.2.2)⟩

/-- A point over `U` strictly inside the top layer `(H, H')` is a measure-theoretic interior point. -/
theorem mem_measureTheoreticInterior_of_top (hS : SlabTrappedRepresentation b E U H H' μ ν)
    {x : Space (m + 1)} (hxU : horizontal x ∈ U) (hx1 : H < x (Fin.last m))
    (hx2 : x (Fin.last m) < H') : x ∈ measureTheoreticInterior E := by
  set O := {z : Space (m + 1) | horizontal z ∈ U ∧ z (Fin.last m) ∈ Ioo H H'}
  have hO : IsOpen O := isOpen_cylinder_Ioo hS.isOpen H H'
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO x ⟨hxU, hx1, hx2⟩
  refine ⟨r, hr, measure_mono_null (fun z hz ↦ ?_) (ae_iff.mp hS.top)⟩
  intro h
  exact hz.2 (h (hrO hz.1).1 (hrO hz.1).2)

/-- A point over `U` strictly inside the bottom layer `(-H', -H)` is a measure-theoretic exterior
point. -/
theorem mem_measureTheoreticExterior_of_bot (hS : SlabTrappedRepresentation b E U H H' μ ν)
    {x : Space (m + 1)} (hxU : horizontal x ∈ U) (hx1 : -H' < x (Fin.last m))
    (hx2 : x (Fin.last m) < -H) : x ∈ measureTheoreticExterior E := by
  set O := {z : Space (m + 1) | horizontal z ∈ U ∧ z (Fin.last m) ∈ Ioo (-H') (-H)}
  have hO : IsOpen O := isOpen_cylinder_Ioo hS.isOpen (-H') (-H)
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO x ⟨hxU, hx1, hx2⟩
  refine ⟨r, hr, measure_mono_null (fun z hz ↦ ?_) (ae_iff.mp hS.bot)⟩
  intro h
  exact h (hrO hz.2).1 (hrO hz.2).2 hz.1

/-- **The phase outside the band.** If every measure-theoretic boundary point over a convex
base `B ⊆ U` lies within `δ` of the level `a`, where `|a| ≤ H`, then over `B` almost every point
above the band lies in `E`, and almost every point below the band lies outside `E`. -/
theorem ae_mem_iff_of_band (hS : SlabTrappedRepresentation b E U H H' μ ν)
    {B : Set (Space m)} (hBc : Convex ℝ B) (hBU : B ⊆ U) {a δ : ℝ}
    (ha : |a| ≤ H) (hδ : 0 ≤ δ)
    (hband : ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ B → |x (Fin.last m)| < H' →
      |x (Fin.last m) - a| ≤ δ) :
    ∀ᵐ x ∂volume, horizontal x ∈ B → |x (Fin.last m)| < H' → δ < |x (Fin.last m) - a| →
      (x ∈ E ↔ a < x (Fin.last m)) := by
  have hH := hS.pos
  have hHH' := hS.lt
  have haH := abs_le.mp ha
  set Vp := {x : Space (m + 1) | horizontal x ∈ B ∧ x (Fin.last m) ∈ Ioo (a + δ) H'} with hVp
  set Vm := {x : Space (m + 1) | horizontal x ∈ B ∧ x (Fin.last m) ∈ Ioo (-H') (a - δ)}
    with hVm
  -- neither band component contains a boundary point
  have hVpb : ∀ x ∈ Vp, x ∉ measureTheoreticBoundary E := by
    intro x hx hxb
    have h1 := hband x hxb hx.1 (abs_lt.mpr ⟨by linarith [hx.2.1], hx.2.2⟩)
    have h2 := (abs_le.mp h1).2
    linarith [hx.2.1]
  have hVmb : ∀ x ∈ Vm, x ∉ measureTheoreticBoundary E := by
    intro x hx hxb
    have h1 := hband x hxb hx.1 (abs_lt.mpr ⟨hx.2.1, by linarith [hx.2.2]⟩)
    have h2 := (abs_le.mp h1).1
    linarith [hx.2.2]
  -- the upper component lies in the interior, the lower one in the exterior
  have hVpI : Vp ⊆ measureTheoreticInterior E := by
    rcases Vp.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · rw [he]; exact empty_subset _
    rcases subset_measureTheoreticInterior_or_exterior
      (convex_cylinder_Ioo hBc (a + δ) H').isPreconnected hVpb with hI | hX
    · exact hI
    · exfalso
      -- a point of `Vp` in the top layer is an interior point
      set t₀ := (max H (a + δ) + H') / 2
      have ht₁ : max H (a + δ) < t₀ := by
        have : max H (a + δ) < H' := max_lt hHH' (by linarith [hx₀.2.2, hx₀.2.1])
        simp only [t₀]; linarith
      have ht₂ : t₀ < H' := by
        have : max H (a + δ) < H' := max_lt hHH' (by linarith [hx₀.2.2, hx₀.2.1])
        simp only [t₀]; linarith
      set p := point (horizontal x₀) t₀
      have hpV : p ∈ Vp := by
        refine ⟨by simpa [p, horizontal_point] using hx₀.1, ?_, ?_⟩
        · simp only [p, last_point]; exact lt_of_le_of_lt (le_max_right _ _) ht₁
        · simp only [p, last_point]; exact ht₂
      have hpI : p ∈ measureTheoreticInterior E := by
        refine hS.mem_measureTheoreticInterior_of_top ?_ ?_ ?_
        · simpa [p, horizontal_point] using hBU hx₀.1
        · simp only [p, last_point]; exact lt_of_le_of_lt (le_max_left _ _) ht₁
        · simp only [p, last_point]; exact ht₂
      exact Set.disjoint_left.mp (disjoint_measureTheoreticInterior_exterior E) hpI (hX hpV)
  have hVmX : Vm ⊆ measureTheoreticExterior E := by
    rcases Vm.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · rw [he]; exact empty_subset _
    rcases subset_measureTheoreticInterior_or_exterior
      (convex_cylinder_Ioo hBc (-H') (a - δ)).isPreconnected hVmb with hI | hX
    · exfalso
      set t₀ := (min (-H) (a - δ) + -H') / 2
      have hlt : -H' < min (-H) (a - δ) :=
        lt_min (by linarith) (by linarith [hx₀.2.2, hx₀.2.1])
      have ht₁ : t₀ < min (-H) (a - δ) := by simp only [t₀]; linarith
      have ht₂ : -H' < t₀ := by simp only [t₀]; linarith
      set p := point (horizontal x₀) t₀
      have hpV : p ∈ Vm := by
        refine ⟨by simpa [p, horizontal_point] using hx₀.1, ?_, ?_⟩
        · simp only [p, last_point]; exact ht₂
        · simp only [p, last_point]; exact lt_of_lt_of_le ht₁ (min_le_right _ _)
      have hpX : p ∈ measureTheoreticExterior E := by
        refine hS.mem_measureTheoreticExterior_of_bot ?_ ?_ ?_
        · simpa [p, horizontal_point] using hBU hx₀.1
        · simp only [p, last_point]; exact ht₂
        · simp only [p, last_point]; exact lt_of_lt_of_le ht₁ (min_le_left _ _)
      exact Set.disjoint_left.mp (disjoint_measureTheoreticInterior_exterior E) (hI hpV) hpX
    · exact hX
  have hnullp : volume (Vp \ E) = 0 :=
    measure_mono_null (fun x (hx : x ∈ Vp \ E) ↦ (⟨hVpI hx.1, hx.2⟩ :
      x ∈ measureTheoreticInterior E \ E)) (volume_measureTheoreticInterior_sdiff E)
  have hnullm : volume (E ∩ Vm) = 0 :=
    measure_mono_null (fun x (hx : x ∈ E ∩ Vm) ↦ (⟨hx.1, hVmX hx.2⟩ :
      x ∈ E ∩ measureTheoreticExterior E)) (volume_inter_measureTheoreticExterior E)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnullp,
    measure_eq_zero_iff_ae_notMem.mp hnullm] with x hxp hxm hxB hxH hxδ
  have hxH' := abs_lt.mp hxH
  rcases lt_or_gt_of_ne (show x (Fin.last m) - a ≠ 0 from fun h0 ↦ by
    rw [h0, abs_zero] at hxδ; linarith) with hneg | hpos
  · rw [abs_of_neg hneg] at hxδ
    have hxV : x ∈ Vm := ⟨hxB, hxH'.1, by linarith⟩
    constructor
    · intro hxE; exact absurd ⟨hxE, hxV⟩ hxm
    · intro hlt; linarith
  · rw [abs_of_pos hpos] at hxδ
    have hxV : x ∈ Vp := ⟨hxB, by linarith, hxH'.2⟩
    constructor
    · intro _; linarith
    · intro _
      by_contra hxE
      exact hxp ⟨hxV, hxE⟩

end SlabTrappedRepresentation

end SerrinEpigraph
