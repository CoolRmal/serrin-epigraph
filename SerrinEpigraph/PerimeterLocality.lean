module

public import SerrinEpigraph.PerimeterRadonGlobal
public import SerrinEpigraph.PerimeterInvariance

/-!
# Locality and compact perturbations of perimeter minimizers

The comparison on concentric balls implies comparison on every open set containing the
compact perturbation. The cancellation below only removes a finite common measure.
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Perimeter measures agree on every open region where the phases agree almost everywhere. -/
theorem perimeter_measure_restrict_eq_of_ae_on {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E D O : Set (Space d)}
    (μ ν : Measure (Space d)) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (hμ : ∀ U, IsOpen U → μ U = variationalPerimeter b E U)
    (hν : ∀ U, IsOpen U → ν U = variationalPerimeter b D U)
    (hO : IsOpen O) (hED : ∀ᵐ x ∂volume, x ∈ O → (x ∈ E ↔ x ∈ D)) :
    μ.restrict O = ν.restrict O := by
  apply Measure.OuterRegular.ext_isOpen
  intro U hU
  rw [Measure.restrict_apply hU.measurableSet, Measure.restrict_apply hU.measurableSet,
    hμ _ (hU.inter hO), hν _ (hU.inter hO)]
  apply variationalPerimeter_congr_ae_on b
  filter_upwards [hED] with x hx
  exact fun hxU ↦ hx hxU.2

/-- Locality also controls measurable pieces of an open region, including annular seams. -/
theorem perimeter_measure_eq_of_subset_ae_region {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E D O A : Set (Space d)}
    (μ ν : Measure (Space d)) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (hμ : ∀ U, IsOpen U → μ U = variationalPerimeter b E U)
    (hν : ∀ U, IsOpen U → ν U = variationalPerimeter b D U)
    (hO : IsOpen O) (hED : ∀ᵐ x ∂volume, x ∈ O → (x ∈ E ↔ x ∈ D))
    (hA : MeasurableSet A) (hAO : A ⊆ O) : μ A = ν A := by
  have he := congrArg (fun ρ : Measure (Space d) ↦ ρ A)
    (perimeter_measure_restrict_eq_of_ae_on b μ ν hμ hν hO hED)
  simpa only [Measure.restrict_apply hA, inter_eq_left.mpr hAO] using he

/-- Cancelling the perimeter outside a compact perturbation transfers a ball comparison
to an arbitrary open set. Neither measure is required to be globally finite. -/
theorem perimeter_comparison_localize {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E D K Ω B : Set (Space d)}
    (μ ν : Measure (Space d)) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (hμ : ∀ U, IsOpen U → μ U = variationalPerimeter b E U)
    (hν : ∀ U, IsOpen U → ν U = variationalPerimeter b D U)
    (hK : IsClosed K) (hΩ : IsOpen Ω) (hB : IsOpen B)
    (hKΩ : K ⊆ Ω) (hKB : K ⊆ B) (hνB : ν B ≠ ⊤)
    (hED : ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D))
    (hcomp : μ B ≤ ν B) : μ Ω ≤ ν Ω := by
  have heq (A : Set (Space d)) (hA : MeasurableSet A) (hAK : A ⊆ Kᶜ) :
      μ A = ν A := perimeter_measure_eq_of_subset_ae_region b μ ν hμ hν
        hK.isOpen_compl hED hA hAK
  have houter : μ (B \ Ω) = ν (B \ Ω) := heq _ (hB.measurableSet.diff hΩ.measurableSet)
    (fun x hx hxK ↦ hx.2 (hKΩ hxK))
  have hfinite : ν (B \ Ω) ≠ ⊤ := ne_top_of_le_ne_top hνB (measure_mono sdiff_subset)
  have hinter : μ (B ∩ Ω) ≤ ν (B ∩ Ω) := by
    rw [← measure_inter_add_sdiff B hΩ.measurableSet (μ := μ),
      ← measure_inter_add_sdiff B hΩ.measurableSet (μ := ν), houter] at hcomp
    exact (ENNReal.add_le_add_iff_right hfinite).mp hcomp
  have hrest : μ (Ω \ B) = ν (Ω \ B) := heq _ (hΩ.measurableSet.diff hB.measurableSet)
    (fun x hx hxK ↦ hx.2 (hKB hxK))
  rw [← measure_inter_add_sdiff Ω hB.measurableSet (μ := μ),
    ← measure_inter_add_sdiff Ω hB.measurableSet (μ := ν), hrest, inter_comm Ω B]
  exact add_le_add hinter le_rfl

/-- Concentric-ball minimality gives the usual open-set comparison for every locally
finite-perimeter competitor differing only on a compact subset of the open set. -/
theorem perimeter_minimality_of_concentric_ball_comparison {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E D K Ω : Set (Space d)}
    (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hPE : ∀ n : ℕ, variationalPerimeter b E (ball 0 ((n : ℝ) + 1)) ≠ ⊤)
    (hPD : ∀ n : ℕ, variationalPerimeter b D (ball 0 ((n : ℝ) + 1)) ≠ ⊤)
    (hmin : ∀ s r : ℝ, 0 < s → r < s →
      (∀ᵐ x ∂volume.restrict (ball 0 s \ closedBall 0 r), x ∈ E ↔ x ∈ D) →
      variationalPerimeter b E (ball 0 s) ≤ variationalPerimeter b D (ball 0 s))
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hED : ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) :
    variationalPerimeter b E Ω ≤ variationalPerimeter b D Ω := by
  let μ := perimeterRadonMeasure b hE hPE
  let ν := perimeterRadonMeasure b hD hPD
  have hμ (U : Set (Space d)) (hU : IsOpen U) : μ U = variationalPerimeter b E U :=
    perimeterRadonMeasure_apply_open b hE hPE hU
  have hν (U : Set (Space d)) (hU : IsOpen U) : ν U = variationalPerimeter b D U :=
    perimeterRadonMeasure_apply_open b hD hPD hU
  obtain ⟨n, hn⟩ := compact_subset_perimeter_ball hK
  have hKB : K ⊆ ball (0 : Space d) (((n + 1 : ℕ) : ℝ) + 1) :=
    hn.trans (ball_subset_ball (by simp))
  have hνB : ν (ball 0 (((n + 1 : ℕ) : ℝ) + 1)) ≠ ⊤ := by
    rw [hν _ isOpen_ball]
    exact hPD (n + 1)
  have hcomp : μ (ball 0 (((n + 1 : ℕ) : ℝ) + 1)) ≤
      ν (ball 0 (((n + 1 : ℕ) : ℝ) + 1)) := by
    rw [hμ _ isOpen_ball, hν _ isOpen_ball]
    apply hmin _ ((n : ℝ) + 1) (by positivity) (by simp)
    apply (ae_restrict_iff' (measurableSet_ball.diff measurableSet_closedBall)).mpr
    filter_upwards [hED] with x hx hxA
    exact hx (fun hxK ↦ hxA.2 (ball_subset_closedBall (hn hxK)))
  rw [← hμ Ω hΩ, ← hν Ω hΩ]
  exact perimeter_comparison_localize b μ ν hμ hν hK.isClosed hΩ isOpen_ball
    hKΩ hKB hνB hED hcomp

end SerrinEpigraph
