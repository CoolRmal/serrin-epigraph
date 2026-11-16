module

public import SerrinEpigraph.PlaneTiltConvergence
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Coordinate invariance of planar gradient-defect convergence
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- The totalized gradient transforms exactly under a linear Euclidean isometry,
including at points where the function is not differentiable. -/
theorem gradient_comp_linearIsometryEquiv {d : ℕ} (v : Space d → ℝ)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (x : Space d) :
    gradient (fun y ↦ v (Q y)) x = Q.symm (gradient v (Q x)) := by
  apply ext_inner_right ℝ
  intro y
  rw [Q.symm.inner_map_eq_flip, inner_gradient_left, inner_gradient_left]
  have he := Q.toContinuousLinearEquiv.comp_right_fderiv (f := v) (x := x)
  exact congrArg (fun L : Space d →L[ℝ] ℝ ↦ L y) he

/-- A Euclidean change of coordinates preserves every integral over an origin-centered ball. -/
theorem setIntegral_closedBall_comp_linearIsometryEquiv {d : ℕ}
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (v : Space d → ℝ) (r : ℝ) :
    (∫ x in closedBall 0 r, v (Q x)) = ∫ x in closedBall 0 r, v x := by
  have hh := (Q.measurePreserving.restrict_preimage
    (s := closedBall 0 r) measurableSet_closedBall).integral_comp
    Q.toHomeomorph.measurableEmbedding v
  simpa only [Q.preimage_closedBall, map_zero] using hh

/-- Every unit normal can be obtained from the vertical unit vector by an exact isometry. -/
theorem exists_linearIsometryEquiv_vertical {m : ℕ} {e : Space (m + 1)} (he : ‖e‖ = 1) :
    ∃ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1), Q (verticalDirection m) = e := by
  exact ⟨(ℝ ∙ (verticalDirection m - e))ᗮ.reflection,
    Submodule.reflection_sub ((norm_verticalDirection m).trans he.symm)⟩

/-- The positive halfspace indicator rotates to the horizontal epigraph indicator. -/
theorem positive_halfspace_indicator_comp {m : ℕ}
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {e : Space (m + 1)}
    (he : Q (verticalDirection m) = e) (σ : ℝ) (x : Space (m + 1)) :
    {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ σ) (Q x) =
      (epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator (fun _ ↦ σ) x := by
  have hi : inner ℝ e (Q x) = x (Fin.last m) := by
    rw [← he, Q.inner_map_map]
    simp [verticalDirection, EuclideanSpace.inner_single_left]
  simp only [indicator_apply, mem_ofPred_eq, hi, epigraph]

/-- The compact directional flux of an arbitrarily oriented halfspace is exactly
its weighted plane trace in orthonormal coordinates. -/
theorem integral_positive_halfspace_indicator_test {m : ℕ}
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {e : Space (m + 1)}
    (hQ : Q (verticalDirection m) = e) {ψ : Space (m + 1) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    {K : Set (Space (m + 1))} (hK : MeasurableSet K) (hs : tsupport ψ ⊆ K) (σ : ℝ) :
    (∫ x in K, {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ σ) x *
      fderiv ℝ ψ x e) = -σ * ∫ y : Space m, ψ (Q (point y 0)) := by
  have hsupport : tsupport (ψ ∘ Q) ⊆ Q ⁻¹' K :=
    (tsupport_comp_subset_preimage ψ Q.continuous).trans (preimage_mono hs)
  have hd (x : Space (m + 1)) : fderiv ℝ (ψ ∘ Q) x (verticalDirection m) =
      fderiv ℝ ψ (Q x) e := by
    have hh := congrArg (fun L : Space (m + 1) →L[ℝ] ℝ ↦ L (verticalDirection m))
      (Q.toContinuousLinearEquiv.comp_right_fderiv (f := ψ) (x := x))
    change fderiv ℝ (ψ ∘ Q) x (verticalDirection m) =
      fderiv ℝ ψ (Q x) (Q (verticalDirection m)) at hh
    simpa only [hQ] using hh
  have ht := integral_halfspace_indicator_vertical_test (hψ.comp Q.contDiff)
    (hc.comp_homeomorph Q.toHomeomorph) hsupport σ
  have he := (Q.measurePreserving.restrict_preimage hK).integral_comp
    Q.toHomeomorph.measurableEmbedding
    (fun x ↦ {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ σ) x *
      fderiv ℝ ψ x e)
  rw [← he]
  convert ht using 1
  · apply setIntegral_congr_fun (hK.preimage Q.continuous.measurable)
    intro x hx
    dsimp only
    rw [positive_halfspace_indicator_comp Q hQ, hd]
  · rfl

/-- The planar calibration argument with an upper mass bound is independent of
the orientation of the limiting halfspace. -/
theorem integral_oriented_gradient_defect_tendsto_zero_of_positive_halfspace_limit_of_mass_bound
    {m : ℕ} {v : ℕ → Space (m + 1) → ℝ} (hv : ∀ j, LocallyLipschitz (v j))
    {B : ℕ → ℝ} (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) (B j))
    {σ : ℝ} (hσ : 0 ≤ σ) {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖v j x - {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ σ) x‖)
        atTop (𝓝 0))
    {A : ℕ → ℝ → ℝ}
    (hbound : ∀ j s, 0 < s → (∫ x in closedBall 0 s, ‖gradient (v j) x‖) ≤ A j s)
    (hmass : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ A j s) atTop
      (𝓝 (σ * (s ^ m * volume.real (closedBall (0 : Space m) 1)))))
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖gradient (v j) x‖ - inner ℝ (gradient (v j) x) e) atTop (𝓝 0) := by
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_vertical he
  have hl (s : ℝ) (hs : 0 < s) : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖v j (Q x) - (epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator (fun _ ↦ σ) x‖)
        atTop (𝓝 0) := by
    convert hlocal s hs using 1
    funext j
    simp_rw [← positive_halfspace_indicator_comp Q hQ σ]
    exact setIntegral_closedBall_comp_linearIsometryEquiv Q
      (fun x ↦ ‖v j x - {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ σ) x‖) s
  have hm (j : ℕ) (s : ℝ) (hs : 0 < s) :
      (∫ x in closedBall 0 s, ‖gradient (fun y ↦ v j (Q y)) x‖) ≤ A j s := by
    simp_rw [gradient_comp_linearIsometryEquiv, Q.symm.norm_map]
    rw [setIntegral_closedBall_comp_linearIsometryEquiv Q (fun x ↦ ‖gradient (v j) x‖) s]
    exact hbound j s hs
  have ht := integral_oriented_gradient_defect_tendsto_zero_of_halfspace_limit_of_mass_bound
    (fun j ↦ (hv j).comp Q.lipschitzWith.locallyLipschitz)
    (fun j x ↦ hval j (Q x)) hσ hl hm hmass hr
  convert ht using 1
  funext j
  simp_rw [Function.comp_def, gradient_comp_linearIsometryEquiv, Q.symm.norm_map,
    Q.symm.inner_map_eq_flip, Q.symm_symm, hQ]
  exact (setIntegral_closedBall_comp_linearIsometryEquiv Q
    (fun x ↦ ‖gradient (v j) x‖ - inner ℝ (gradient (v j) x) e) r).symm

/-- The planar calibration argument is independent of the orientation of the limiting
halfspace. Its inputs concern the actual functions and actual gradient masses. -/
theorem integral_oriented_gradient_defect_tendsto_zero_of_positive_halfspace_limit
    {m : ℕ} {v : ℕ → Space (m + 1) → ℝ} (hv : ∀ j, LocallyLipschitz (v j))
    {B : ℕ → ℝ} (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) (B j))
    {σ : ℝ} (hσ : 0 ≤ σ) {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖v j x - {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ σ) x‖)
        atTop (𝓝 0))
    (hmass : ∀ s : ℝ, 0 < s → Tendsto
      (fun j ↦ ∫ x in closedBall 0 s, ‖gradient (v j) x‖) atTop
      (𝓝 (σ * (s ^ m * volume.real (closedBall (0 : Space m) 1)))))
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖gradient (v j) x‖ - inner ℝ (gradient (v j) x) e) atTop (𝓝 0) :=
  integral_oriented_gradient_defect_tendsto_zero_of_positive_halfspace_limit_of_mass_bound
    hv hval hσ he hlocal (fun _ _ _ ↦ le_rfl) hmass hr

end SerrinEpigraph
