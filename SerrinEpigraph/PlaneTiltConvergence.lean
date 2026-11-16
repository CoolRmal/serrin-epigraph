module

public import SerrinEpigraph.PlaneTiltIntegral
public import SerrinEpigraph.GraphVerticalFlux

/-!
# Vanishing oriented defects for a planar phase limit
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- The horizontal coordinate inclusion preserves the Euclidean norm. -/
theorem norm_point_zero {m : ℕ} (y : Space m) : ‖point y 0‖ = ‖y‖ := by
  have hh : ‖point y 0‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_point_point, real_inner_self_eq_norm_sq]
    ring
  nlinarith [norm_nonneg (point y 0), norm_nonneg y]

/-- A compact test against an upper-halfspace indicator gives exactly the negative
weighted trace on the horizontal plane. -/
theorem integral_halfspace_indicator_vertical_test
    {m : ℕ} {ψ : Space (m + 1) → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) {K : Set (Space (m + 1))} (hs : tsupport ψ ⊆ K)
    (σ : ℝ) :
    (∫ x in K, (epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator (fun _ ↦ σ) x *
      fderiv ℝ ψ x (verticalDirection m)) = -σ * ∫ y : Space m, ψ (point y 0) := by
  have he : (∫ x in K,
      (epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator (fun _ ↦ σ) x *
        fderiv ℝ ψ x (verticalDirection m)) =
      ∫ x, (epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator (fun _ ↦ σ) x *
        fderiv ℝ ψ x (verticalDirection m) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hx (hs hh)), zero_apply, mul_zero]
  rw [he]
  have hind (x : Space (m + 1)) :
      (epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator (fun _ ↦ σ) x *
          fderiv ℝ ψ x (verticalDirection m) =
        (epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator
          (fun x ↦ σ * verticalDerivative ψ x) x := by
    by_cases hx : x ∈ epigraph (fun _ : Space m ↦ (0 : ℝ)) <;>
      simp [hx, verticalDerivative]
  simp_rw [hind]
  rw [integral_indicator (isOpen_epigraph continuous_const).measurableSet,
    integral_const_mul, integral_epigraph_verticalDerivative continuous_const hψ hc]
  ring

/-- A nonnegative plane trace equal to one on a ball has at least that ball's mass. -/
theorem plane_trace_integral_ge_ball_volume
    {m : ℕ} {ψ : Space (m + 1) → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    {r : ℝ} (hone : ∀ x ∈ closedBall (0 : Space (m + 1)) r, ψ x = 1) :
    volume.real (closedBall (0 : Space m) r) ≤ ∫ y : Space m, ψ (point y 0) := by
  have hcont : Continuous (fun y : Space m ↦ ψ (point y 0)) :=
    hψ.comp (pointContinuousLinearMap.continuous.comp (continuous_id.prodMk continuous_const))
  have hsupp : HasCompactSupport (fun y : Space m ↦ ψ (point y 0)) := by
    simpa only [zero_add] using hasCompactSupport_graph_section
      (b := fun _ : Space m ↦ (0 : ℝ)) hc 0
  have he : (∫ y in closedBall (0 : Space m) r, ψ (point y 0)) =
      volume.real (closedBall (0 : Space m) r) := by
    calc
      _ = ∫ _y in closedBall (0 : Space m) r, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_closedBall
        intro y hy
        exact hone _ (by simpa only [mem_closedBall, dist_zero_right, norm_point_zero] using hy)
      _ = _ := by simp
  rw [← he]
  exact setIntegral_le_integral (hcont.integrable_of_hasCompactSupport hsupp)
    (Eventually.of_forall (fun y ↦ hψ0 _))

/-- An upper mass bound with the exact planar limit and local phase convergence
force the oriented gradient defect to vanish; exact gradient-mass convergence is unnecessary. -/
theorem integral_oriented_gradient_defect_tendsto_zero_of_halfspace_limit_of_mass_bound
    {m : ℕ} {v : ℕ → Space (m + 1) → ℝ} (hv : ∀ j, LocallyLipschitz (v j))
    {B : ℕ → ℝ} (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) (B j))
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖v j x - (epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator (fun _ ↦ σ) x‖)
        atTop (𝓝 0))
    {A : ℕ → ℝ → ℝ}
    (hbound : ∀ j s, 0 < s → (∫ x in closedBall 0 s, ‖gradient (v j) x‖) ≤ A j s)
    (hmass : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ A j s) atTop
      (𝓝 (σ * (s ^ m * volume.real (closedBall (0 : Space m) 1)))))
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖gradient (v j) x‖ - inner ℝ (gradient (v j) x) (verticalDirection m))
        atTop (𝓝 0) := by
  let ω := volume.real (closedBall (0 : Space m) 1)
  let M : ℝ → ℝ := fun s ↦ σ * (s ^ m * ω)
  have hM : Continuous M := by unfold M; fun_prop
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j ↦ ha.trans_le (integral_nonneg (fun x ↦
      oriented_gradient_defect_nonneg (gradient (v j) x) (norm_verticalDirection m))))
  · intro b hb
    let s : ℕ → ℝ := fun k ↦ r + 1 / ((k : ℝ) + 1)
    have hsr (k : ℕ) : r < s k := by
      exact lt_add_of_pos_right r (by positivity)
    have hst : Tendsto s atTop (𝓝 r) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := r)).add tendsto_one_div_add_atTop_nhds_zero_nat
    have hsmall : Tendsto (fun k ↦ M (s k) - M r) atTop (𝓝 0) := by
      simpa only [Function.comp_def, sub_self] using
        ((hM.tendsto r).comp hst).sub_const (M r)
    obtain ⟨k, hk⟩ := (hsmall.eventually_lt_const (half_pos hb)).exists
    let ψ : ContDiffBump (0 : Space (m + 1)) := ⟨r, s k, hr, hsr k⟩
    have hψ : ContDiff ℝ 1 (ψ : Space (m + 1) → ℝ) := ψ.contDiff
    have hs : tsupport (ψ : Space (m + 1) → ℝ) ⊆ closedBall 0 (s k) := by
      rw [ψ.tsupport_eq]
    have htrace := plane_trace_integral_ge_ball_volume ψ.continuous ψ.hasCompactSupport
      (fun _ ↦ ψ.nonneg) (fun _ hx ↦ ψ.one_of_mem_closedBall hx)
    have hvolume : σ * volume.real (closedBall (0 : Space m) r) = M r := by
      rw [Measure.addHaar_real_closedBall' volume (0 : Space m) hr.le]
      simp only [finrank_euclideanSpace_fin, M, ω]
    have htrace' : M r ≤ σ * ∫ y : Space m, ψ (point y 0) := by
      rw [← hvolume]
      exact mul_le_mul_of_nonneg_left htrace hσ
    have hp : IntegrableOn
        ((epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator (fun _ ↦ σ))
        (closedBall 0 (s k)) :=
      (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 (s k))).indicator
        (isOpen_epigraph continuous_const).measurableSet
    have hf := integral_cutoff_gradient_tendsto_of_integral_norm_sub_tendsto hv hval
      hψ ψ.hasCompactSupport (isCompact_closedBall 0 (s k)) hs hp (verticalDirection m)
      (hlocal (s k) (hr.trans (hsr k)))
    rw [integral_halfspace_indicator_vertical_test hψ ψ.hasCompactSupport hs σ,
      neg_mul, neg_neg] at hf
    have hu := (hmass (s k) (hr.trans (hsr k))).sub hf
    have hlim : M (s k) - σ * ∫ y : Space m, ψ (point y 0) < b := by
      linarith
    filter_upwards [hu.eventually_lt_const hlim] with j hj
    have hi := integral_oriented_gradient_defect_le_mass_add_test (hv j) (hval j)
      hψ ψ.hasCompactSupport (isCompact_closedBall 0 r) (isCompact_closedBall 0 (s k))
      (closedBall_subset_closedBall (hsr k).le) hs
      (fun _ ↦ ⟨ψ.nonneg, ψ.le_one⟩) (fun _ hx ↦ ψ.one_of_mem_closedBall hx)
      (norm_verticalDirection m)
    have he := setIntegral_inner_gradient_mul_eq_neg_of_locallyLipschitz
      (hv j) (hval j) hψ ψ.hasCompactSupport (isCompact_closedBall 0 (s k)) hs
      (verticalDirection m)
    have hbA := hbound j (s k) (hr.trans (hsr k))
    linarith

/-- Exact ball masses and local integral convergence to a weighted planar phase
force the oriented gradient defect to vanish on every fixed positive-radius ball. -/
theorem integral_oriented_gradient_defect_tendsto_zero_of_halfspace_limit
    {m : ℕ} {v : ℕ → Space (m + 1) → ℝ} (hv : ∀ j, LocallyLipschitz (v j))
    {B : ℕ → ℝ} (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) (B j))
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖v j x - (epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator (fun _ ↦ σ) x‖)
        atTop (𝓝 0))
    (hmass : ∀ s : ℝ, 0 < s → Tendsto
      (fun j ↦ ∫ x in closedBall 0 s, ‖gradient (v j) x‖) atTop
      (𝓝 (σ * (s ^ m * volume.real (closedBall (0 : Space m) 1)))))
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖gradient (v j) x‖ - inner ℝ (gradient (v j) x) (verticalDirection m))
        atTop (𝓝 0) :=
  integral_oriented_gradient_defect_tendsto_zero_of_halfspace_limit_of_mass_bound
    hv hval hσ hlocal (fun _ _ _ ↦ le_rfl) hmass hr

end SerrinEpigraph
