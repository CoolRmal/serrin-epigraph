module

public import SerrinEpigraph.PerimeterRadonGlobal
public import SerrinEpigraph.BoundaryWeakInequality

/-!
# Smooth product testing for finite-perimeter phases

This is the distributional product calculation used for radial cutting competitors.
-/

public section

open Set MeasureTheory InnerProductSpace Filter
open scoped Topology CompactlySupported

namespace SerrinEpigraph

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The smooth product rule controls a weighted indicator by its weighted perimeter mass
and the derivative of the scalar weight. -/
theorem perimeter_weighted_test_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {ν : Space d → Space d}
    (hν : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ G : C_c(Space d, Space d), ContDiff ℝ 1 (G : Space d → Space d) →
      tsupport G ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x) =
        ∫ x, inner ℝ (G x) (ν x) ∂μ)
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    {F : Space d → Space d} (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (hs : tsupport (fun x ↦ φ x • F x) ⊆ Ω) (hunit : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * φ x * fieldDivergence b F x‖ ≤
      (∫ x, φ x ∂μ) +
        ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * ‖gradient φ x‖ * ‖F x‖ := by
  let χ := E.indicator (fun _ : Space d ↦ (1 : ℝ))
  have hχ (x : Space d) : 0 ≤ χ x := by by_cases hx : x ∈ E <;> simp [χ, hx]
  have hgrad : Continuous (gradient φ) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hdc : HasCompactSupport (fieldDivergence b F) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hnot
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hnot)
  have hAi : Integrable (fun x ↦ χ x * φ x * fieldDivergence b F x) := by
    have hi := (hφ.continuous.mul (fieldDivergence_continuous b hF))
      |>.integrable_of_hasCompactSupport (μ := volume) hdc.mul_left
    convert hi.indicator hE using 1
    ext x
    by_cases hx : x ∈ E <;> simp [χ, hx]
  have hqci : HasCompactSupport (fun x ↦ inner ℝ (gradient φ x) (F x)) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hnot
    exact hx (by
      change inner ℝ (gradient φ x) (F x) = 0
      rw [image_eq_zero_of_notMem_tsupport hnot, inner_zero_right])
  have hQi : Integrable (fun x ↦ χ x * inner ℝ (gradient φ x) (F x)) := by
    have hi := (hgrad.inner hF.continuous).integrable_of_hasCompactSupport (μ := volume) hqci
    convert hi.indicator hE using 1
    ext x
    by_cases hx : x ∈ E <;> simp [χ, hx]
  have hCi : Integrable (fun x ↦ χ x * ‖gradient φ x‖ * ‖F x‖) := by
    have hi := (hgrad.norm.mul hF.continuous.norm)
      |>.integrable_of_hasCompactSupport (μ := volume) hc.norm.mul_left
    convert hi.indicator hE using 1
    ext x
    by_cases hx : x ∈ E <;> simp [χ, hx]
  let G : C_c(Space d, Space d) := ⟨⟨fun x ↦ φ x • F x,
    hφ.continuous.smul hF.continuous⟩, hc.smul_left (f := φ)⟩
  have hGs : tsupport G ⊆ Ω := hs
  have hid := hdist G (hφ.smul hF) hGs
  have hdiv (x : Space d) : χ x * fieldDivergence b G x =
      χ x * φ x * fieldDivergence b F x + χ x * inner ℝ (gradient φ x) (F x) := by
    change χ x * fieldDivergence b (fun y ↦ φ y • F y) x = _
    rw [fieldDivergence_fun_smul b (hφ.differentiable_one x) (hF.differentiable_one x)]
    ring
  change -(∫ x, χ x * fieldDivergence b G x) = _ at hid
  simp_rw [hdiv] at hid
  rw [integral_add hAi hQi] at hid
  have hφi : Integrable φ μ := Integrable.of_bound hφ.continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x ↦ by rw [Real.norm_of_nonneg (hφrange x).1]; exact (hφrange x).2)
  have hinnerBound : ∀ᵐ x ∂μ, ‖inner ℝ (G x) (ν x)‖ ≤ φ x := by
    filter_upwards [hν] with x hx
    calc
      ‖inner ℝ (G x) (ν x)‖ ≤ ‖G x‖ * ‖ν x‖ := norm_inner_le_norm _ _
      _ = φ x * ‖F x‖ := by
        change ‖φ x • F x‖ * ‖ν x‖ = _
        rw [norm_smul, Real.norm_of_nonneg (hφrange x).1, hx, mul_one]
      _ ≤ φ x := by nlinarith [(hφrange x).1, hunit x]
  have hnI : ‖∫ x, inner ℝ (G x) (ν x) ∂μ‖ ≤ ∫ x, φ x ∂μ :=
    norm_integral_le_of_norm_le hφi hinnerBound
  have hnQ : ‖∫ x, χ x * inner ℝ (gradient φ x) (F x)‖ ≤
      ∫ x, χ x * ‖gradient φ x‖ * ‖F x‖ := by
    apply norm_integral_le_of_norm_le hCi
    exact Eventually.of_forall fun x ↦ by
      rw [norm_mul, Real.norm_of_nonneg (hχ x)]
      exact (mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (hχ x)).trans_eq
        (mul_assoc _ _ _).symm
  have heq : (∫ x, χ x * φ x * fieldDivergence b F x) =
      -(∫ x, inner ℝ (G x) (ν x) ∂μ) -
        ∫ x, χ x * inner ℝ (gradient φ x) (F x) := by linarith
  change ‖∫ x, χ x * φ x * fieldDivergence b F x‖ ≤ _
  rw [heq]
  exact (norm_sub_le _ _).trans (by rw [norm_neg]; exact add_le_add hnI hnQ)

end SerrinEpigraph
