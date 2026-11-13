module

public import SerrinEpigraph.IntegrationByParts
public import SerrinEpigraph.IntegralLimitTesting

/-!
# Directional derivative tests controlled by gradient mass
-/

public section

open MeasureTheory Metric
open scoped Topology

namespace SerrinEpigraph

/-- Compactly supported directional integration by parts on a containing compact set. -/
theorem setIntegral_mul_fderiv_eq_neg {d : ℕ} {v ψ : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    {K : Set (Space d)} (hs : tsupport ψ ⊆ K) (a : Space d) :
    (∫ x in K, v x * fderiv ℝ ψ x a) = -∫ x in K, fderiv ℝ v x a * ψ x := by
  have hleft : (∫ x in K, v x * fderiv ℝ ψ x a) =
      ∫ x, v x * fderiv ℝ ψ x a := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : fderiv ℝ ψ x a = 0 := Function.notMem_support.mp (fun hh ↦
      hx (hs ((tsupport_fderiv_apply_subset ℝ a) (subset_tsupport _ hh))))
    rw [hz, mul_zero]
  have hright : (∫ x in K, fderiv ℝ v x a * ψ x) =
      ∫ x, fderiv ℝ v x a * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : ψ x = 0 := Function.notMem_support.mp (fun hh ↦ hx (hs (subset_tsupport _ hh)))
    rw [hz, mul_zero]
  rw [hleft, hright]
  exact integral_mul_fderiv_eq_neg_of_hasCompactSupport isOpen_univ hv.contDiffOn hψ hc
    (Set.subset_univ _) a

/-- Unit-bounded compact directional tests are controlled by the local gradient mass. -/
theorem norm_setIntegral_mul_fderiv_le_gradient {d : ℕ} {v ψ : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    {K : Set (Space d)} (hK : IsCompact K) (hs : tsupport ψ ⊆ K)
    (hb : ∀ x, ‖ψ x‖ ≤ 1) (a : Space d) :
    ‖∫ x in K, v x * fderiv ℝ ψ x a‖ ≤ ‖a‖ * ∫ x in K, ‖gradient v x‖ := by
  rw [setIntegral_mul_fderiv_eq_neg hv hψ hc hs a, norm_neg]
  have hg : Continuous (fun x ↦ ‖gradient v x‖) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (hv.continuous_fderiv one_ne_zero).norm
  calc
    ‖∫ x in K, fderiv ℝ v x a * ψ x‖ ≤
        ∫ x in K, ‖fderiv ℝ v x a * ψ x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in K, ‖a‖ * ‖gradient v x‖ := by
      apply integral_mono
        ((((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
          hψ.continuous).norm.continuousOn.integrableOn_compact hK)
        ((continuous_const.mul hg).continuousOn.integrableOn_compact hK)
      intro x
      simp only [Pi.mul_apply]
      rw [norm_mul]
      calc
        ‖fderiv ℝ v x a‖ * ‖ψ x‖ ≤ ‖fderiv ℝ v x a‖ * 1 :=
          mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
        _ ≤ ‖a‖ * ‖gradient v x‖ := by
          rw [mul_one]
          calc
            ‖fderiv ℝ v x a‖ ≤ ‖fderiv ℝ v x‖ * ‖a‖ := (fderiv ℝ v x).le_opNorm a
            _ = ‖a‖ * ‖gradient v x‖ := by
              simp only [gradient, LinearIsometryEquiv.norm_map, mul_comm]
    _ = ‖a‖ * ∫ x in K, ‖gradient v x‖ := integral_const_mul _ _

/-- The directional test bound survives integral convergence of smooth approximations. -/
theorem norm_setIntegral_mul_fderiv_le_of_smooth_limit
    {d : ℕ} {F : ℕ → Space d → ℝ} {v ψ : Space d → ℝ}
    (hF : ∀ j, ContDiff ℝ 1 (F j)) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) {K : Set (Space d)} (hK : IsCompact K)
    (hs : tsupport ψ ⊆ K) (hb : ∀ x, ‖ψ x‖ ≤ 1) (a : Space d)
    (hv : IntegrableOn v K) (C B : ℝ) (hderiv : ∀ x, ‖fderiv ℝ ψ x a‖ ≤ C)
    (ht : Filter.Tendsto (fun j ↦ ∫ x in K, ‖F j x - v x‖) Filter.atTop (𝓝 0))
    (hgrad : Filter.Tendsto (fun j ↦ ∫ x in K, ‖gradient (F j) x‖)
      Filter.atTop (𝓝 B)) :
    ‖∫ x in K, v x * fderiv ℝ ψ x a‖ ≤ ‖a‖ * B := by
  have htest := integral_mul_tendsto_of_integral_norm_sub_tendsto
    (volume.restrict K) F v (fun x ↦ fderiv ℝ ψ x a) C
    (fun j ↦ (hF j).continuous.continuousOn.integrableOn_compact hK) hv
    (((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable)
    hderiv ht
  apply le_of_tendsto_of_tendsto htest.norm (hgrad.const_mul ‖a‖)
  exact Filter.Eventually.of_forall
    (fun j ↦ norm_setIntegral_mul_fderiv_le_gradient (hF j) hψ hc hK hs hb a)

end SerrinEpigraph
