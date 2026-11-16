module

public import SerrinEpigraph.PerimeterRadonFunctional
public import SerrinEpigraph.PerimeterRadonSigned

/-!
# Distributional directional derivatives as signed measures

Finite variational perimeter produces actual finite signed measures representing the
distributional derivatives. The construction uses the divergence functional and signed Riesz
representation, rather than a structure assuming these measures exist.
-/

public section

open MeasureTheory
open scoped Topology BoundedContinuousFunction CompactlySupported

namespace SerrinEpigraph

/-- A scalar bounded function multiplied by a fixed vector, as a continuous linear map. -/
@[expose] noncomputable def scalarVectorField {d : ℕ} (v : Space d) :
    (Space d →ᵇ ℝ) →L[ℝ] (Space d →ᵇ Space d) :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).compLeftContinuousBounded (Space d)

@[simp] theorem scalarVectorField_apply {d : ℕ} (v : Space d)
    (f : Space d →ᵇ ℝ) (x : Space d) : scalarVectorField v f x = f x • v := rfl

/-- Fixed-vector multiplication costs precisely the vector norm, or less in a trivial domain. -/
theorem norm_scalarVectorField_le {d : ℕ} (v : Space d) :
    ‖scalarVectorField v‖ ≤ ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
  intro f
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg v) (norm_nonneg f))).mpr
  intro x
  rw [scalarVectorField_apply, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg v)

/-- The divergence of a scalar test times a fixed vector is its directional derivative. -/
theorem fieldDivergence_smul_const {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {f : Space d → ℝ}
    (hf : Differentiable ℝ f) (v x : Space d) :
    fieldDivergence b (fun y ↦ f y • v) x = fderiv ℝ f x v := by
  have hsum := congrArg (fderiv ℝ f x) (b.sum_repr' v)
  simp only [map_sum, map_smul, smul_eq_mul] at hsum
  simpa only [fieldDivergence, fderiv_smul_const (hf x),
    ContinuousLinearMap.smulRight_apply, inner_smul_right, mul_comm] using hsum

set_option backward.isDefEq.respectTransparency false in
/-- Every directional derivative of a finite-perimeter indicator is represented by a finite
signed measure, with the expected variation bound and exact distributional identity. -/
theorem exists_directional_perimeter_measure {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hP : variationalPerimeter b E Ω ≠ ⊤) (v : Space d) :
    ∃ σ : SignedMeasure (Space d),
      σ.variation Set.univ ≤ ENNReal.ofReal ((variationalPerimeter b E Ω).toReal * ‖v‖) ∧
      ∀ f : C_c(Space d, ℝ), ContDiff ℝ 1 (f : Space d → ℝ) → tsupport f ⊆ Ω →
        -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fderiv ℝ f x v) =
          ∫ᵛ x, f x ∂<•σ := by
  obtain ⟨L, hL, hnorm⟩ := exists_perimeterDistribution_extension b hE hP
  let Lv := L.comp (scalarVectorField v)
  obtain ⟨σ, hσ, hrep⟩ := exists_signed_riesz_measure (0 : Space d) Lv
  refine ⟨σ, hσ.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le L (scalarVectorField v)).trans
      (mul_le_mul hnorm (norm_scalarVectorField_le v) (norm_nonneg _)
        ENNReal.toReal_nonneg)
  · intro f hf hs
    let F := scalarVectorField v (compactToBoundedLinear f)
    have hFc : ContDiff ℝ 1 (F : Space d → Space d) := hf.smul_const v
    have hFs : tsupport F ⊆ tsupport f := tsupport_smul_subset_left f (fun _ ↦ v)
    have hFcomp : HasCompactSupport (F : Space d → Space d) :=
      f.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hFs
    let Ft : perimeterTestSubmodule Ω := ⟨F, hFc, hFcomp, hFs.trans hs⟩
    have he := hL Ft
    change L F = -∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x *
      fieldDivergence b (fun y ↦ f y • v) x at he
    simp_rw [fieldDivergence_smul_const b hf.differentiable_one] at he
    exact he.symm.trans (hrep f)

end SerrinEpigraph
