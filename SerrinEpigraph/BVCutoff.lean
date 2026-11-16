module

public import SerrinEpigraph.BVProduct
public import SerrinEpigraph.FixedWidthCutoff

/-!
# Radial cutoff costs for finite-perimeter phases
-/

public section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology CompactlySupported

namespace SerrinEpigraph

/-- A function equal to a constant on an open region has zero gradient there. -/
theorem gradient_eq_zero_of_eqOn_open {d : ℕ} {φ : Space d → ℝ} {O : Set (Space d)}
    {c : ℝ} (hO : IsOpen O) (hφ : EqOn φ (fun _ ↦ c) O) {x : Space d} (hx : x ∈ O) :
    gradient φ x = 0 := by
  have he : φ =ᶠ[𝓝 x] fun _ ↦ c := Filter.eventuallyEq_of_mem (hO.mem_nhds hx) hφ
  simp [gradient, he.fderiv_eq]

/-- A scalar weight vanishing outside a set has integral at most the measure of that set. -/
theorem integral_weight_le_measure {d : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {φ : Space d → ℝ} (hφ : Continuous φ) (hval : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    {A : Set (Space d)} (hA : MeasurableSet A) (hzero : ∀ x ∉ A, φ x = 0) :
    (∫ x, φ x ∂μ) ≤ μ.real A := by
  have hi : Integrable φ μ := Integrable.of_bound hφ.aestronglyMeasurable 1
    (Eventually.of_forall fun x ↦ by rw [Real.norm_of_nonneg (hval x).1]; exact (hval x).2)
  rw [← integral_indicator_one hA]
  apply integral_mono hi ((integrable_const (1 : ℝ)).indicator hA)
  intro x
  by_cases hx : x ∈ A
  · simpa [hx] using (hval x).2
  · simp [hx, hzero x hx]

/-- The cutoff derivative contributes only the volume of its transition annulus. -/
theorem integral_phase_cutoff_gradient_le {d : ℕ} {E : Set (Space d)}
    (hE : MeasurableSet E) {r ε C : ℝ} (_hε : 0 < ε) (_hC : 0 ≤ C)
    {φ : Space d → ℝ} (_hφ : ContDiff ℝ 1 φ)
    (hs : tsupport φ ⊆ ball 0 (r + ε))
    (hone : ∀ x ∈ ball 0 r, φ x = 1) (hgrad : ∀ x, ‖gradient φ x‖ ≤ C / ε)
    {F : Space d → Space d} (hunit : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * ‖gradient φ x‖ * ‖F x‖) ≤
      C / ε * volume.real (E ∩ (ball 0 (r + ε) \ ball 0 r)) := by
  let A := E ∩ (ball (0 : Space d) (r + ε) \ ball 0 r)
  have hA : MeasurableSet A := hE.inter (measurableSet_ball.diff measurableSet_ball)
  have hAV : volume A ≠ ⊤ := ne_top_of_le_ne_top measure_ball_ne_top
    (measure_mono fun _ hx ↦ hx.2.1)
  have hAi : Integrable (A.indicator (fun _ ↦ C / ε)) volume :=
    (integrableOn_const (C := C / ε) hAV).integrable_indicator hA
  have hpoint (x : Space d) :
      E.indicator (fun _ ↦ (1 : ℝ)) x * ‖gradient φ x‖ * ‖F x‖ ≤
        A.indicator (fun _ ↦ C / ε) x := by
    by_cases hxE : x ∈ E
    · by_cases hxi : x ∈ ball (0 : Space d) r
      · have hz := gradient_eq_zero_of_eqOn_open isOpen_ball hone hxi
        simp [A, hxE, hxi, hz]
      · by_cases hxo : x ∈ ball (0 : Space d) (r + ε)
        · simp only [indicator_of_mem hxE, one_mul,
            indicator_of_mem (show x ∈ A from ⟨hxE, hxo, hxi⟩)]
          exact (mul_le_mul_of_nonneg_left (hunit x) (norm_nonneg _)).trans
            (by simpa using hgrad x)
        · have hz : gradient φ x = 0 := by
            simp [gradient, fderiv_of_notMem_tsupport ℝ (fun hh ↦ hxo (hs hh))]
          simp [A, hxE, hxo, hz]
    · simp [A, hxE]
  have hle := integral_mono_of_nonneg
    (Eventually.of_forall fun x ↦ mul_nonneg
      (mul_nonneg (by by_cases hx : x ∈ E <;> simp [hx]) (norm_nonneg _)) (norm_nonneg _))
    hAi (Eventually.of_forall hpoint)
  simpa only [integral_indicator_const _ hA, smul_eq_mul, mul_comm (volume.real A)] using hle

/-- A radial cutoff gives a quantitative distributional test bound for the truncated phase. -/
theorem perimeter_inside_cutoff_test_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {ν : Space d → Space d} (hν : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ G : C_c(Space d, Space d), ContDiff ℝ 1 (G : Space d → Space d) →
      tsupport G ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x) =
        ∫ x, inner ℝ (G x) (ν x) ∂μ)
    {r ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hball : ball 0 (r + ε) ⊆ Ω)
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hs : tsupport φ ⊆ ball 0 (r + ε)) (hone : ∀ x ∈ ball 0 r, φ x = 1)
    (hval : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hgrad : ∀ x, ‖gradient φ x‖ ≤ C / ε)
    {F : Space d → Space d} (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (hunit : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * φ x * fieldDivergence b F x‖ ≤
      μ.real (ball 0 (r + ε)) +
        C / ε * volume.real (E ∩ (ball 0 (r + ε) \ ball 0 r)) := by
  have hw := perimeter_weighted_test_bound b hE μ hν hdist hφ hval hF hc
    ((tsupport_smul_subset_left φ F).trans (hs.trans hball)) hunit
  exact hw.trans (add_le_add
    (integral_weight_le_measure μ hφ.continuous hval measurableSet_ball
      (fun x hx ↦ image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh))))
    (integral_phase_cutoff_gradient_le hE hε hC hφ hs hone hgrad hunit))

end SerrinEpigraph
