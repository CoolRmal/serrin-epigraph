module

public import SerrinEpigraph.PerimeterRadonLocal

/-!
# A Radon perimeter measure for locally finite perimeter

The finite-region constructions are compatible on nested balls. Their monotone limit yields
one locally finite regular measure on the whole Euclidean space.
-/

public section

open MeasureTheory
open scoped Topology CompactlySupported ENNReal

namespace SerrinEpigraph

/-- Countable sums commute with a monotone supremum of nonnegative sequences. -/
theorem tsum_iSup_nat_of_monotone (f : ℕ → ℕ → ℝ≥0∞) (hf : Monotone f) :
    (∑' i, ⨆ n, f n i) = ⨆ n, ∑' i, f n i := by
  have he := lintegral_iSup (μ := Measure.count) (f := f)
    (fun _ ↦ measurable_of_countable _) hf
  simpa only [lintegral_count] using he

/-- The monotone limit of an increasing measure sequence, constructed by countable additivity. -/
@[expose] noncomputable def monotoneMeasureLimit {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) (hμ : Monotone μ) : Measure X :=
  Measure.ofMeasurable (fun s _ ↦ ⨆ n, μ n s) (by simp) (by
    intro s hs hd
    simp_rw [measure_iUnion hd hs]
    exact (tsum_iSup_nat_of_monotone (fun n i ↦ μ n (s i))
      (fun n m hnm i ↦ hμ hnm (s i))).symm)

theorem monotoneMeasureLimit_apply {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) (hμ : Monotone μ) {s : Set X} (hs : MeasurableSet s) :
    monotoneMeasureLimit μ hμ s = ⨆ n, μ n s := Measure.ofMeasurable_apply s hs

/-- Every compact set is contained in one ball of the integer-radius exhaustion. -/
theorem compact_subset_perimeter_ball {d : ℕ} {K : Set (Space d)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ Metric.ball 0 ((n : ℝ) + 1) := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Space d)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  exact ⟨n, hr.trans (Metric.ball_subset_ball (by linarith))⟩

/-- The original divergence supremum is exhausted by its intersections with expanding balls. -/
theorem variationalPerimeter_eq_iSup_inter_ball {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E U : Set (Space d)) :
    variationalPerimeter b E U =
      ⨆ n : ℕ, variationalPerimeter b E (U ∩ Metric.ball 0 ((n : ℝ) + 1)) := by
  apply le_antisymm
  · refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦
      iSup_le fun hs ↦ iSup_le fun hunit ↦ ?_
    obtain ⟨n, hn⟩ := compact_subset_perimeter_ball hc
    exact le_iSup_of_le n (le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hc
      (le_iSup_of_le (Set.subset_inter hs hn) (le_iSup_of_le hunit le_rfl)))))
  · exact iSup_le fun n ↦ variationalPerimeter_mono b E Set.inter_subset_left

/-- A finite measure concentrated on an open set is determined by its open subregion values. -/
theorem measure_restrict_eq_of_open_values {d : ℕ} {μ ν : Measure (Space d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {Ω : Set (Space d)} (hΩ : IsOpen Ω)
    (hzero : μ Ωᶜ = 0)
    (heq : ∀ U, IsOpen U → U ⊆ Ω → μ U = ν U) : ν.restrict Ω = μ := by
  have hself : μ.restrict Ω = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]
    exact hzero)
  apply Measure.OuterRegular.ext_isOpen
  intro U hU
  calc
    (ν.restrict Ω) U = ν (U ∩ Ω) := Measure.restrict_apply hU.measurableSet
    _ = μ (U ∩ Ω) := (heq _ (hU.inter hΩ) Set.inter_subset_right).symm
    _ = (μ.restrict Ω) U := (Measure.restrict_apply hU.measurableSet).symm
    _ = μ U := congrArg (fun m : Measure (Space d) ↦ m U) hself

/-- Locally finite variational perimeter defines an actual locally finite Radon measure whose
value on every open set is exactly the original divergence supremum. -/
theorem exists_global_perimeter_measure {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    (hP : ∀ n : ℕ, variationalPerimeter b E (Metric.ball 0 ((n : ℝ) + 1)) ≠ ⊤) :
    ∃ μ : Measure (Space d), IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
      ∀ U, IsOpen U → μ U = variationalPerimeter b E U := by
  let Ω : ℕ → Set (Space d) := fun n ↦ Metric.ball 0 ((n : ℝ) + 1)
  have hex (n : ℕ) : ∃ μ : Measure (Space d), IsFiniteMeasure μ ∧
      μ (Ω n)ᶜ = 0 ∧ ∀ U, IsOpen U → U ⊆ Ω n → μ U = variationalPerimeter b E U := by
    obtain ⟨σ, hm, -, hz, hd⟩ := exists_perimeter_vector_measure_concentrated b hE
      Metric.isOpen_ball.measurableSet (hP n)
    let : IsFiniteMeasure σ.variation := ⟨by rw [hm]; exact lt_top_iff_ne_top.mpr (hP n)⟩
    exact ⟨σ.variation, inferInstance, hz,
      fun U hU hs ↦ variation_eq_variationalPerimeter_of_representation b σ hd hU hs⟩
  choose m hmfinite hmzero hmlocal using hex
  have hΩmono : Monotone Ω := by
    intro n k hnk
    exact Metric.ball_subset_ball (add_le_add (Nat.cast_le.mpr hnk) (le_refl (1 : ℝ)))
  have hmself (n : ℕ) : (m n).restrict (Ω n) = m n :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hmzero n)
  have hmopen (n : ℕ) (U : Set (Space d)) (hU : IsOpen U) :
      m n U = variationalPerimeter b E (U ∩ Ω n) := by
    calc
      m n U = ((m n).restrict (Ω n)) U := congrArg (fun μ : Measure (Space d) ↦ μ U)
        (hmself n).symm
      _ = m n (U ∩ Ω n) := Measure.restrict_apply hU.measurableSet
      _ = variationalPerimeter b E (U ∩ Ω n) :=
        hmlocal n _ (hU.inter Metric.isOpen_ball) Set.inter_subset_right
  have hmcompat {n k : ℕ} (hnk : n ≤ k) : (m k).restrict (Ω n) = m n := by
    let : IsFiniteMeasure (m n) := hmfinite n
    let : IsFiniteMeasure (m k) := hmfinite k
    apply measure_restrict_eq_of_open_values Metric.isOpen_ball (hmzero n)
    intro U hU hs
    rw [hmlocal n U hU hs, hmlocal k U hU (hs.trans (hΩmono hnk))]
  have hmmono : Monotone m := by
    intro n k hnk
    rw [← hmcompat hnk]
    exact Measure.restrict_le_self
  let μ := monotoneMeasureLimit m hmmono
  have hμopen (U : Set (Space d)) (hU : IsOpen U) : μ U = variationalPerimeter b E U := by
    rw [monotoneMeasureLimit_apply m hmmono hU.measurableSet]
    simp_rw [hmopen _ U hU]
    exact (variationalPerimeter_eq_iSup_inter_ball b E U).symm
  have hμfinite : IsLocallyFiniteMeasure μ := by
    constructor
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    have hx : x ∈ Ω n := by
      change dist x 0 < (n : ℝ) + 1
      rw [dist_zero_right]
      linarith
    refine ⟨Ω n, Metric.isOpen_ball.mem_nhds hx, ?_⟩
    rw [hμopen _ Metric.isOpen_ball]
    exact lt_top_iff_ne_top.mpr (hP n)
  let : IsLocallyFiniteMeasure μ := hμfinite
  exact ⟨μ, hμfinite, inferInstance, hμopen⟩

/-- Each finite open region of the global perimeter measure has a constructed unit polar vector
and the distributional gradient identity against that very measure's restriction. -/
theorem exists_local_polar_for_perimeter_measure {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hΩ : IsOpen Ω) (hP : variationalPerimeter b E Ω ≠ ⊤)
    (μ : Measure (Space d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → μ U = variationalPerimeter b E U) :
    ∃ ν : Space d → Space d,
      Integrable ν (μ.restrict Ω) ∧ (∀ᵐ x ∂μ.restrict Ω, ‖ν x‖ = 1) ∧
      ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
        tsupport F ⊆ Ω →
        -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
          ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω := by
  obtain ⟨σ, hmass, -, hzero, hdist⟩ :=
    exists_perimeter_vector_measure_concentrated b hE hΩ.measurableSet hP
  let : IsFiniteMeasure σ.variation := ⟨by rw [hmass]; exact lt_top_iff_ne_top.mpr hP⟩
  let : IsFiniteMeasure (μ.restrict Ω) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hμ Ω hΩ]
    exact lt_top_iff_ne_top.mpr hP⟩
  have hself : σ.variation.restrict Ω = σ.variation :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hzero)
  have heq : μ.restrict Ω = σ.variation := by
    apply Measure.OuterRegular.ext_isOpen
    intro U hU
    calc
      (μ.restrict Ω) U = μ (U ∩ Ω) := Measure.restrict_apply hU.measurableSet
      _ = variationalPerimeter b E (U ∩ Ω) := hμ _ (hU.inter hΩ)
      _ = σ.variation (U ∩ Ω) :=
        (variation_eq_variationalPerimeter_of_representation b σ hdist
          (hU.inter hΩ) Set.inter_subset_right).symm
      _ = (σ.variation.restrict Ω) U := (Measure.restrict_apply hU.measurableSet).symm
      _ = σ.variation U := congrArg (fun m : Measure (Space d) ↦ m U) hself
  have hi := integrable_vectorPolarDensity b σ
  have hn := norm_vectorPolarDensity_ae b σ
  refine ⟨vectorPolarDensity b σ, heq.symm ▸ hi, heq.symm ▸ hn, ?_⟩
  intro F hF hs
  rw [heq]
  refine (hdist F hF hs).trans ?_
  nth_rw 1 [← withDensity_vectorPolarDensity b σ]
  exact integral_withDensity_inner_of_ae_bounded hi (hn.mono fun _ h ↦ h.le)
    F.continuous.measurable (norm_nonneg F.toBoundedContinuousFunction)
    F.toBoundedContinuousFunction.norm_coe_le_norm

/-- The perimeter measure constructed from local finiteness of the original divergence supremum. -/
@[expose] noncomputable def perimeterRadonMeasure {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    (hP : ∀ n : ℕ, variationalPerimeter b E (Metric.ball 0 ((n : ℝ) + 1)) ≠ ⊤) :
    Measure (Space d) := Classical.choose (exists_global_perimeter_measure b hE hP)

instance perimeterRadonMeasure_isLocallyFinite {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    (hP : ∀ n : ℕ, variationalPerimeter b E (Metric.ball 0 ((n : ℝ) + 1)) ≠ ⊤) :
    IsLocallyFiniteMeasure (perimeterRadonMeasure b hE hP) :=
  (Classical.choose_spec (exists_global_perimeter_measure b hE hP)).1

/-- The constructed Radon measure agrees with variational perimeter on every open set. -/
theorem perimeterRadonMeasure_apply_open {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    (hP : ∀ n : ℕ, variationalPerimeter b E (Metric.ball 0 ((n : ℝ) + 1)) ≠ ⊤)
    {U : Set (Space d)} (hU : IsOpen U) :
    perimeterRadonMeasure b hE hP U = variationalPerimeter b E U :=
  (Classical.choose_spec (exists_global_perimeter_measure b hE hP)).2.2 U hU

/-- Agreement with variational perimeter on open sets uniquely determines the Radon measure. -/
theorem perimeterRadonMeasure_unique {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    (hP : ∀ n : ℕ, variationalPerimeter b E (Metric.ball 0 ((n : ℝ) + 1)) ≠ ⊤)
    (μ : Measure (Space d)) [μ.OuterRegular]
    (hμ : ∀ U, IsOpen U → μ U = variationalPerimeter b E U) :
    μ = perimeterRadonMeasure b hE hP :=
  Measure.OuterRegular.ext_isOpen fun U hU ↦
    (hμ U hU).trans (perimeterRadonMeasure_apply_open b hE hP hU).symm

end SerrinEpigraph
