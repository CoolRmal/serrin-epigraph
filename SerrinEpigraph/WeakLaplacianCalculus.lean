module

public import SerrinEpigraph.WeakBochner
public import SerrinEpigraph.WeakViscosity

/-!
# Calculus for continuous weak Laplacians
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- The Laplacian equation tested against compactly supported interior C1 functions. -/
@[expose] def HasWeakLaplacian {d : ℕ} (Ω : Set (Space d)) (v F : Space d → ℝ) : Prop :=
  ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ x, inner ℝ (gradient v x) (gradient φ x)) = -(∫ x, F x * φ x)

variable {d : ℕ} {Ω : Set (Space d)} {v w F G : Space d → ℝ}

/-- A classical C2 function satisfies the weak equation for its Laplacian. -/
theorem hasWeakLaplacian_of_contDiffOn (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 2 v Ω) :
    HasWeakLaplacian Ω v (Δ v) := fun _φ hφ hc hs ↦
  integral_inner_gradient_eq_neg_laplacian_mul hΩ hv hφ hc hs

/-- Multiplication by a real constant commutes with the weak Laplacian. -/
theorem HasWeakLaplacian.const_mul (heq : HasWeakLaplacian Ω v F)
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω) (a : ℝ) :
    HasWeakLaplacian Ω (fun x ↦ a * v x) (fun x ↦ a * F x) := by
  intro φ hφ hc hs
  have hpoint (x : Space d) :
      inner ℝ (gradient (fun y ↦ a * v y) x) (gradient φ x) =
        a * inner ℝ (gradient v x) (gradient φ x) := by
    by_cases hx : x ∈ Ω
    · have hvd := (hv.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
      simp only [gradient, fderiv_const_mul hvd, map_smul, real_inner_smul_left]
    · simp [gradient, fderiv_of_notMem_tsupport ℝ (fun hh ↦ hx (hs hh))]
  simp_rw [hpoint, integral_const_mul, heq φ hφ hc hs, mul_assoc, integral_const_mul]
  ring

/-- Addition commutes with continuous weak Laplacians. -/
theorem HasWeakLaplacian.add (heqv : HasWeakLaplacian Ω v F)
    (heqw : HasWeakLaplacian Ω w G) (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hw : ContDiffOn ℝ 1 w Ω)
    (hF : ContinuousOn F Ω) (hG : ContinuousOn G Ω) :
    HasWeakLaplacian Ω (fun x ↦ v x + w x) (fun x ↦ F x + G x) := by
  intro φ hφ hc hs
  have hiV := integrable_inner_gradient_of_hasCompactSupport (μ := volume) hΩ hv hφ hc hs
  have hiW := integrable_inner_gradient_of_hasCompactSupport (μ := volume) hΩ hw hφ hc hs
  have hiF : Integrable (fun x ↦ F x * φ x) :=
    integrable_mul_of_tsupport_subset hF hφ.continuous hc hs
  have hiG : Integrable (fun x ↦ G x * φ x) :=
    integrable_mul_of_tsupport_subset hG hφ.continuous hc hs
  have hpoint (x : Space d) :
      inner ℝ (gradient (fun y ↦ v y + w y) x) (gradient φ x) =
        inner ℝ (gradient v x) (gradient φ x) + inner ℝ (gradient w x) (gradient φ x) := by
    by_cases hx : x ∈ Ω
    · simp only [gradient, fderiv_fun_add
        ((hv.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx))
        ((hw.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)), map_add,
        inner_add_left]
    · simp [gradient, fderiv_of_notMem_tsupport ℝ (fun hh ↦ hx (hs hh))]
  simp_rw [hpoint, add_mul]
  rw [integral_add hiV hiW, heqv φ hφ hc hs, heqw φ hφ hc hs, integral_add hiF hiG]
  ring

/-- The product rule for C1 functions with continuous weak Laplacians. -/
theorem HasWeakLaplacian.mul (heqv : HasWeakLaplacian Ω v F)
    (heqw : HasWeakLaplacian Ω w G) (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hw : ContDiffOn ℝ 1 w Ω)
    (hF : ContinuousOn F Ω) (hG : ContinuousOn G Ω) :
    HasWeakLaplacian Ω (fun x ↦ v x * w x)
      (fun x ↦ w x * F x + v x * G x + 2 * inner ℝ (gradient v x) (gradient w x)) := by
  intro φ hφ hc hs
  have hvt := contDiff_mul_of_tsupport_subset hΩ hv hφ hs
  have hwt := contDiff_mul_of_tsupport_subset hΩ hw hφ hs
  have hvs : tsupport (fun x ↦ v x * φ x) ⊆ Ω := tsupport_mul_subset_right.trans hs
  have hws : tsupport (fun x ↦ w x * φ x) ⊆ Ω := tsupport_mul_subset_right.trans hs
  have hpv : ContinuousOn (gradient v) Ω :=
    (toDual ℝ (Space d)).symm.continuous.comp_continuousOn
      (hv.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hpw : ContinuousOn (gradient w) Ω :=
    (toDual ℝ (Space d)).symm.continuous.comp_continuousOn
      (hw.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hiV := integrable_inner_gradient_of_hasCompactSupport (μ := volume)
    hΩ hv hwt hc.mul_left hws
  have hiW := integrable_inner_gradient_of_hasCompactSupport (μ := volume)
    hΩ hw hvt hc.mul_left hvs
  have hiF : Integrable (fun x ↦ w x * F x * φ x) :=
    integrable_mul_of_tsupport_subset (hw.continuousOn.mul hF) hφ.continuous hc hs
  have hiG : Integrable (fun x ↦ v x * G x * φ x) :=
    integrable_mul_of_tsupport_subset (hv.continuousOn.mul hG) hφ.continuous hc hs
  have hiC : Integrable (fun x ↦ 2 * inner ℝ (gradient v x) (gradient w x) * φ x) :=
    integrable_mul_of_tsupport_subset (continuousOn_const.mul (hpv.inner hpw))
      hφ.continuous hc hs
  have hpoint (x : Space d) :
      inner ℝ (gradient (fun y ↦ v y * w y) x) (gradient φ x) =
        (inner ℝ (gradient v x) (gradient (fun y ↦ w y * φ y) x) +
          inner ℝ (gradient w x) (gradient (fun y ↦ v y * φ y) x)) -
          2 * inner ℝ (gradient v x) (gradient w x) * φ x := by
    by_cases hx : x ∈ Ω
    · have hvd := (hv.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
      have hwd := (hw.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
      rw [gradient_mul_at hvd hwd, gradient_mul_at hwd (hφ.differentiable_one x),
        gradient_mul_at hvd (hφ.differentiable_one x)]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm (gradient v x) (gradient w x)]
      ring
    · have hxφ : x ∉ tsupport φ := fun hh ↦ hx (hs hh)
      have hxv : x ∉ tsupport (fun y ↦ v y * φ y) := fun hh ↦ hx (hvs hh)
      have hxw : x ∉ tsupport (fun y ↦ w y * φ y) := fun hh ↦ hx (hws hh)
      simp [gradient, fderiv_of_notMem_tsupport ℝ hxφ, fderiv_of_notMem_tsupport ℝ hxv,
        fderiv_of_notMem_tsupport ℝ hxw, image_eq_zero_of_notMem_tsupport hxφ]
  simp_rw [hpoint]
  have hiVW : Integrable (fun x ↦
      inner ℝ (gradient v x) (gradient (fun y ↦ w y * φ y) x) +
        inner ℝ (gradient w x) (gradient (fun y ↦ v y * φ y) x)) := hiV.add hiW
  have hiFG : Integrable (fun x ↦ w x * F x * φ x + v x * G x * φ x) := hiF.add hiG
  rw [integral_sub hiVW hiC, integral_add hiV hiW,
    heqv _ hwt hc.mul_left hws, heqw _ hvt hc.mul_left hvs]
  have hsrc : (fun x ↦ (w x * F x + v x * G x +
      2 * inner ℝ (gradient v x) (gradient w x)) * φ x) =
      fun x ↦ (w x * F x * φ x + v x * G x * φ x) +
        2 * inner ℝ (gradient v x) (gradient w x) * φ x := by funext x; ring
  have hFswap : (fun x ↦ F x * (w x * φ x)) = fun x ↦ w x * F x * φ x := by
    funext x; ring
  have hGswap : (fun x ↦ G x * (v x * φ x)) = fun x ↦ v x * G x * φ x := by
    funext x; ring
  rw [hsrc, hFswap, hGswap, integral_add hiFG hiC, integral_add hiF hiG]
  ring

/-- Continuous weak Laplacians are nonpositive at local maxima. -/
theorem HasWeakLaplacian.nonpos_of_isLocalMax (heq : HasWeakLaplacian Ω v F)
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω) (hF : ContinuousOn F Ω)
    {x : Space d} (hx : x ∈ Ω) (hmax : IsLocalMax v x) : F x ≤ 0 := by
  have ht := weak_laplacian_le_at_upper_test hΩ hv hF heq
    (ψ := fun _ ↦ (0 : ℝ)) contDiff_const hx (by simpa only [sub_zero] using hmax)
  simpa using ht

end SerrinEpigraph
