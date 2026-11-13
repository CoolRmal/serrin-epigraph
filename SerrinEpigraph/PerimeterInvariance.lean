module

public import SerrinEpigraph.VariationalPerimeter
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Coordinate and representative invariance of variational perimeter
-/

public section

open MeasureTheory Metric
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- The basis expression for divergence is the intrinsic linear trace. -/
theorem fieldDivergence_eq_trace {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (F : Space d → Space d) (x : Space d) :
    fieldDivergence b F x = LinearMap.trace ℝ (Space d) (fderiv ℝ F x).toLinearMap := by
  exact (LinearMap.trace_eq_sum_inner (fderiv ℝ F x).toLinearMap b).symm

/-- Divergence is independent of the orthonormal basis used to compute it. -/
theorem fieldDivergence_basis_independent {d : ℕ}
    (b c : OrthonormalBasis (Fin d) ℝ (Space d)) (F : Space d → Space d) :
    fieldDivergence b F = fieldDivergence c F := by
  funext x
  rw [fieldDivergence_eq_trace, fieldDivergence_eq_trace]

/-- Variational perimeter is independent of the orthonormal basis. -/
theorem variationalPerimeter_basis_independent {d : ℕ}
    (b c : OrthonormalBasis (Fin d) ℝ (Space d)) (E Ω : Set (Space d)) :
    variationalPerimeter b E Ω = variationalPerimeter c E Ω := by
  unfold variationalPerimeter
  simp only [fieldDivergence_basis_independent b c]

/-- Changing a phase on a null set inside the test domain preserves its variational perimeter. -/
theorem variationalPerimeter_congr_ae_on {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E D Ω : Set (Space d)}
    (h : ∀ᵐ x ∂volume, x ∈ Ω → (x ∈ E ↔ x ∈ D)) :
    variationalPerimeter b E Ω = variationalPerimeter b D Ω := by
  unfold variationalPerimeter
  apply iSup_congr
  intro F
  apply iSup_congr
  intro hF
  apply iSup_congr
  intro hc
  apply iSup_congr
  intro hs
  apply iSup_congr
  intro hb
  congr 2
  apply integral_congr_ae
  filter_upwards [h] with x hx
  by_cases hxΩ : x ∈ Ω
  · have he := hx hxΩ
    by_cases hxE : x ∈ E
    · simp [hxE, he.mp hxE]
    · have hxD : x ∉ D := fun hh ↦ hxE (he.mpr hh)
      simp [hxE, hxD]
  · have hz : fderiv ℝ F x = 0 := fderiv_of_notMem_tsupport ℝ
      (fun hh ↦ hxΩ (hs hh))
    simp [fieldDivergence, hz]

end SerrinEpigraph
