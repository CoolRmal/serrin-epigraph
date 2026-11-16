module

public import SerrinEpigraph.BernsteinEstimate

/-!
# Weak Bochner calculus for an inhomogeneous Poisson equation
-/

public section
noncomputable section

open Set MeasureTheory InnerProductSpace Filter Metric
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- Two derivatives of a scalar function give one derivative of its gradient. -/
theorem gradient_contDiffOn_of_two {d : ℕ} {v : Space d → ℝ} {Ω : Set (Space d)}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 2 v Ω) :
    ContDiffOn ℝ 1 (gradient v) Ω :=
  (toDual ℝ (Space d)).symm.contDiff.comp_contDiffOn
    (hv.fderiv_of_isOpen hΩ (m := 1) (by norm_num))

/-- The Hessian square is continuous without a third derivative. -/
theorem hessianSquare_continuousOn_of_two {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v : Space d → ℝ} {Ω : Set (Space d)}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 2 v Ω) : ContinuousOn (hessianSquare b v) Ω := by
  apply continuousOn_finsetSum
  intro i _
  have hd : ContDiffOn ℝ 1 (fun x ↦ fderiv ℝ v x (b i)) Ω :=
    (hv.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).clm_apply contDiffOn_const
  exact ((toDual ℝ (Space d)).symm.continuous.comp_continuousOn
    (hd.continuousOn_fderiv_of_isOpen hΩ le_rfl)).norm.pow 2

/-- A C2 Poisson solution has the differentiated equation in the weak sense. -/
theorem hasWeakLaplacian_directional_of_poisson {d : ℕ} {v F : Space d → ℝ}
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (hF : ContDiffOn ℝ 1 F Ω) (heq : ∀ x ∈ Ω, (Δ v) x = F x) (ξ : Space d) :
    HasWeakLaplacian Ω (fun x ↦ fderiv ℝ v x ξ) (fun x ↦ fderiv ℝ F x ξ) := by
  intro φ hφ hc hs
  have hh := integral_inner_gradient_directional_eq_source_derivative (μ := volume)
    hΩ hv hF.neg hφ hc hs
    (fun x hx ↦ by rw [heq x hx]) ξ
  rw [hh, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  simp only [fderiv_fun_neg, neg_apply, neg_mul]

/-- The weak equation for half a square includes an arbitrary continuous source. -/
theorem HasWeakLaplacian.half_sq {d : ℕ} {v F : Space d → ℝ} {Ω : Set (Space d)}
    (heq : HasWeakLaplacian Ω v F) (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hF : ContinuousOn F Ω) :
    HasWeakLaplacian Ω (fun x ↦ v x ^ 2 / 2)
      (fun x ↦ ‖gradient v x‖ ^ 2 + v x * F x) := by
  have hh := (heq.mul heq hΩ hv hv hF hF).const_mul hΩ (hv.mul hv) (1 / 2)
  convert hh using 1
  · funext x; ring
  · funext x
    rw [real_inner_self_eq_norm_sq]
    ring

/-- The Poisson Bochner identity uses C2 regularity and a C1 source, with no
unjustified third derivative of the solution. -/
theorem hasWeakLaplacian_half_gradient_norm_sq_of_poisson {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v F : Space d → ℝ} {Ω : Set (Space d)}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 2 v Ω) (hF : ContDiffOn ℝ 1 F Ω)
    (heq : ∀ x ∈ Ω, (Δ v) x = F x) :
    HasWeakLaplacian Ω (fun x ↦ ‖gradient v x‖ ^ 2 / 2)
      (fun x ↦ hessianSquare b v x + inner ℝ (gradient v x) (gradient F x)) := by
  let w := fun i x ↦ fderiv ℝ v x (b i)
  let K := fun i x ↦ w i x ^ 2 / 2
  have hw (i : Fin d) : ContDiffOn ℝ 1 (w i) Ω :=
    (hv.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have hK (i : Fin d) : ContDiffOn ℝ 1 (K i) Ω := (hw i).pow 2 |>.div_const 2
  have hDF (i : Fin d) : ContinuousOn (fun x ↦ fderiv ℝ F x (b i)) Ω :=
    (hF.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hsource (i : Fin d) : ContinuousOn
      (fun x ↦ ‖gradient (w i) x‖ ^ 2 + w i x * fderiv ℝ F x (b i)) Ω := by
    have hgrad := (toDual ℝ (Space d)).symm.continuous.comp_continuousOn
      ((hw i).continuousOn_fderiv_of_isOpen hΩ le_rfl)
    exact (hgrad.norm.pow 2).add ((hw i).continuousOn.mul (hDF i))
  have hKi (i : Fin d) := (hasWeakLaplacian_directional_of_poisson hΩ hv hF heq (b i)).half_sq
    hΩ (hw i) (hDF i)
  intro φ hφ hc hs
  have hpair (x : Space d) :
      inner ℝ (gradient (fun y ↦ ‖gradient v y‖ ^ 2 / 2) x) (gradient φ x) =
        ∑ i, inner ℝ (gradient (K i) x) (gradient φ x) := by
    by_cases hx : x ∈ Ω
    · have hdiff (i : Fin d) : DifferentiableAt ℝ (K i) x :=
        ((hK i).differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
      have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (hdiff i).hasFDerivAt)
      have hfunc : (fun y ↦ ‖gradient v y‖ ^ 2 / 2) = fun y ↦ ∑ i, K i y := by
        funext y
        exact half_gradient_norm_sq_eq_sum b v y
      rw [hfunc]
      simp only [gradient, hsum.fderiv, map_sum, sum_inner]
    · simp [gradient, fderiv_of_notMem_tsupport ℝ (fun hh ↦ hx (hs hh))]
  have hiL (i : Fin d) : Integrable
      (fun x ↦ inner ℝ (gradient (K i) x) (gradient φ x)) :=
    integrable_inner_gradient_of_hasCompactSupport hΩ (hK i) hφ hc hs
  have hiR (i : Fin d) : Integrable
      (fun x ↦ (‖gradient (w i) x‖ ^ 2 + w i x * fderiv ℝ F x (b i)) * φ x) :=
    integrable_mul_of_tsupport_subset (hsource i) hφ.continuous hc hs
  simp_rw [hpair]
  rw [integral_finsetSum _ (fun i _ ↦ hiL i)]
  simp_rw [show ∀ i, (∫ x, inner ℝ (gradient (K i) x) (gradient φ x)) =
    -(∫ x, (‖gradient (w i) x‖ ^ 2 + w i x * fderiv ℝ F x (b i)) * φ x) from
      fun i ↦ hKi i φ hφ hc hs]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ ↦ hiR i)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [← Finset.sum_mul, Finset.sum_add_distrib, inner_gradient_eq_sum_fderiv b]
  rfl

end SerrinEpigraph
