module

public import SerrinEpigraph.PerimeterInvariance
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Lower semicontinuity of variational perimeter
-/

public section

open MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- The divergence of a C¹ vector field is continuous. -/
theorem fieldDivergence_continuous {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {F : Space d → Space d}
    (hF : ContDiff ℝ 1 F) : Continuous (fieldDivergence b F) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.inner
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)

/-- Divergence vanishes outside the topological support of its field. -/
theorem fieldDivergence_zero_of_notMem_tsupport {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (F : Space d → Space d)
    {x : Space d} (hx : x ∉ tsupport F) : fieldDivergence b F x = 0 := by
  simp [fieldDivergence, fderiv_of_notMem_tsupport ℝ hx]

/-- Local integral convergence of indicators passes to each compact divergence test. -/
theorem integral_indicator_divergence_tendsto {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E : ℕ → Set (Space d))
    (D Ω : Set (Space d)) (hE : ∀ j, MeasurableSet (E j)) (hD : MeasurableSet D)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E j).indicator (fun _ ↦ (1 : ℝ)) x - D.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {F : Space d → Space d} (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ Ω) :
    Tendsto (fun j ↦ ∫ x, (E j).indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x)
      atTop (𝓝 (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x)) := by
  have hcont := fieldDivergence_continuous b hF
  have hsupport : tsupport (fieldDivergence b F) ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hn)
  have hcompact : HasCompactSupport (fieldDivergence b F) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hcont
  have htest := integral_mul_tendsto_of_integral_norm_sub_tendsto
    (volume.restrict (tsupport F))
    (fun j ↦ (E j).indicator (fun _ ↦ (1 : ℝ))) (D.indicator (fun _ ↦ (1 : ℝ)))
    (fieldDivergence b F) C
    (fun j ↦ (continuousOn_const.integrableOn_compact hc).indicator (hE j))
    ((continuousOn_const.integrableOn_compact hc).indicator hD)
    hcont.aestronglyMeasurable hC (ht (tsupport F) hc hs)
  have he (A : Set (Space d)) :
      (∫ x in tsupport F, A.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
      ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fieldDivergence_zero_of_notMem_tsupport b F hx, mul_zero]
  simpa only [he] using htest

/-- Variational perimeter is lower semicontinuous under local integral convergence of indicators. -/
theorem variationalPerimeter_le_liminf {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E : ℕ → Set (Space d))
    (D Ω : Set (Space d)) (hE : ∀ j, MeasurableSet (E j)) (hD : MeasurableSet D)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E j).indicator (fun _ ↦ (1 : ℝ)) x - D.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0)) :
    variationalPerimeter b D Ω ≤ liminf (fun j ↦ variationalPerimeter b (E j) Ω) atTop := by
  unfold variationalPerimeter
  refine iSup_le (fun F ↦ iSup_le (fun hF ↦ iSup_le (fun hc ↦
    iSup_le (fun hs ↦ iSup_le (fun hb ↦ ?_)))))
  have htest := ENNReal.tendsto_ofReal
    (integral_indicator_divergence_tendsto b E D Ω hE hD ht hF hc hs).norm
  rw [← htest.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall (fun j ↦ le_iSup_of_le F (le_iSup_of_le hF
    (le_iSup_of_le hc (le_iSup_of_le hs (le_iSup_of_le hb le_rfl))))))

end SerrinEpigraph
