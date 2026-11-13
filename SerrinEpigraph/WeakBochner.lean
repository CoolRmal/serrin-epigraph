module

public import SerrinEpigraph.WeakLinearization
public import SerrinEpigraph.WeakQuotient
public import SerrinEpigraph.StressEnergy

/-!
# The Bochner identity with only two derivatives of the solution
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter
open scoped Topology

namespace SerrinEpigraph

/-- Product differentiation expressed through real gradients. -/
theorem gradient_mul_at {d : ℕ} {v φ : Space d → ℝ} {x : Space d}
    (hv : DifferentiableAt ℝ v x) (hφ : DifferentiableAt ℝ φ x) :
    gradient (fun y ↦ v y * φ y) x = φ x • gradient v x + v x • gradient φ x := by
  simp only [gradient, fderiv_fun_mul hv hφ, map_add, map_smul]
  exact add_comm _ _

/-- The gradient of half the square of a real function. -/
theorem gradient_half_sq_at {d : ℕ} {v : Space d → ℝ} {x : Space d}
    (hv : DifferentiableAt ℝ v x) :
    gradient (fun y ↦ v y ^ 2 / 2) x = v x • gradient v x := by
  have hd := (hv.hasFDerivAt.pow 2).smul_const (1 / 2 : ℝ)
  change HasFDerivAt (fun y ↦ v y ^ 2 * (1 / 2)) _ x at hd
  simp only [one_div, ← div_eq_mul_inv] at hd
  have he : fderiv ℝ (fun y ↦ v y ^ 2 / 2) x = v x • fderiv ℝ v x := by
    rw [hd.fderiv]
    ext z
    simp
    ring
  simp only [gradient, he, map_smul]

/-- Testing the linearized equation by the derivative times a test function gives
the weak equation for half its square. No second derivative of that derivative is needed. -/
theorem weak_half_square_identity {d : ℕ} {v a φ : Space d → ℝ} {Ω : Set (Space d)}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω) (ha : ContinuousOn a Ω)
    (hweak : ∀ ψ : Space d → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x, inner ℝ (gradient v x) (gradient ψ x)) = ∫ x, a x * v x * ψ x)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x, inner ℝ (gradient (fun y ↦ v y ^ 2 / 2) x) (gradient φ x)) =
      ∫ x, (a x * v x ^ 2 - ‖gradient v x‖ ^ 2) * φ x := by
  have htest := contDiff_mul_of_tsupport_subset hΩ hv hφ hs
  have htests : tsupport (fun x ↦ v x * φ x) ⊆ Ω := tsupport_mul_subset_right.trans hs
  have hp : ContinuousOn (gradient v) Ω :=
    (toDual ℝ (Space d)).symm.continuous.comp_continuousOn
      (hv.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hiG : Integrable (fun x ↦ ‖gradient v x‖ ^ 2 * φ x) :=
    integrable_mul_of_tsupport_subset (hp.norm.pow 2) hφ.continuous hc hs
  have hiA : Integrable (fun x ↦ a x * v x ^ 2 * φ x) :=
    integrable_mul_of_tsupport_subset (ha.mul (hv.continuousOn.pow 2)) hφ.continuous hc hs
  have hiTest := integrable_inner_gradient_of_hasCompactSupport (μ := volume) hΩ hv
    htest hc.mul_left htests
  have hpoint (x : Space d) :
      inner ℝ (gradient (fun y ↦ v y ^ 2 / 2) x) (gradient φ x) =
        inner ℝ (gradient v x) (gradient (fun y ↦ v y * φ y) x) -
          ‖gradient v x‖ ^ 2 * φ x := by
    by_cases hx : x ∈ Ω
    · have hvx := (hv.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
      rw [gradient_half_sq_at hvx, gradient_mul_at hvx (hφ.differentiable_one x)]
      simp only [real_inner_smul_left, inner_add_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      ring
    · have hxφ : x ∉ tsupport φ := fun hh ↦ hx (hs hh)
      have hxt : x ∉ tsupport (fun y ↦ v y * φ y) := fun hh ↦ hx (htests hh)
      simp [gradient, fderiv_of_notMem_tsupport ℝ hxφ, fderiv_of_notMem_tsupport ℝ hxt,
        image_eq_zero_of_notMem_tsupport hxφ]
  simp_rw [hpoint]
  rw [integral_sub hiTest hiG, hweak _ htest hc.mul_left htests]
  have he : (fun x ↦ a x * v x * (v x * φ x)) = fun x ↦ a x * v x ^ 2 * φ x := by
    funext x
    ring
  rw [he, ← integral_sub hiA hiG]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ by dsimp only; ring)

/-- Squared Hessian norm, written as the sum of squared gradients of directional derivatives. -/
@[expose] def hessianSquare {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (u : Space d → ℝ) (x : Space d) : ℝ :=
  ∑ i, ‖gradient (fun y ↦ fderiv ℝ u y (b i)) x‖ ^ 2

/-- Half the gradient norm squared is the sum of half the squared coordinate derivatives. -/
theorem half_gradient_norm_sq_eq_sum {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (u : Space d → ℝ) (x : Space d) :
    ‖gradient u x‖ ^ 2 / 2 = ∑ i, (fderiv ℝ u x (b i)) ^ 2 / 2 := by
  have he := b.sum_inner_mul_inner (gradient u x) (gradient u x)
  rw [real_inner_self_eq_norm_sq] at he
  simp only [inner_gradient_left, inner_gradient_right, RCLike.conj_to_real, ← sq] at he
  rw [← Finset.sum_div, he]

/-- The weak Bochner identity follows by summing the weak equations for coordinate squares. -/
theorem Hypotheses.weak_bochner_identity {m : ℕ} {g : Space m → ℝ}
    {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ epigraph g) :
    (∫ x, inner ℝ (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x) (gradient φ x)) =
      ∫ x, (deriv f (u x) * ‖gradient u x‖ ^ 2 - hessianSquare b u x) * φ x := by
  let v := fun i x ↦ fderiv ℝ u x (b i)
  let K := fun i x ↦ v i x ^ 2 / 2
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hv (i : Fin (m + 1)) : ContDiffOn ℝ 1 (v i) (epigraph g) :=
    (h.solution_contDiffOn.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have hK (i : Fin (m + 1)) : ContDiffOn ℝ 1 (K i) (epigraph g) := (hv i).pow 2 |>.div_const 2
  have ha : ContinuousOn (fun x ↦ deriv f (u x)) (epigraph g) :=
    ((h.reaction_contDiffOn.mono Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl).comp h.solution_contDiffOn.continuousOn h.positive
  have he (i : Fin (m + 1)) := weak_half_square_identity hΩ (hv i) ha
    (fun ψ hψ hψc hψs ↦ h.weak_linearized_equation hψ hψc hψs (b i)) hφ hc hs
  have hpair (x : Space (m + 1)) :
      inner ℝ (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x) (gradient φ x) =
        ∑ i, inner ℝ (gradient (K i) x) (gradient φ x) := by
    by_cases hx : x ∈ epigraph g
    · have hdiff (i : Fin (m + 1)) : DifferentiableAt ℝ (K i) x :=
        ((hK i).differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
      have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (hdiff i).hasFDerivAt)
      have hfunc : (fun y ↦ ‖gradient u y‖ ^ 2 / 2) = fun y ↦ ∑ i, K i y := by
        funext y
        exact half_gradient_norm_sq_eq_sum b u y
      rw [hfunc]
      simp only [gradient, hsum.fderiv, map_sum, sum_inner]
    · have hxφ : x ∉ tsupport φ := fun hh ↦ hx (hs hh)
      simp [gradient, fderiv_of_notMem_tsupport ℝ hxφ]
  have hiL (i : Fin (m + 1)) : Integrable
      (fun x ↦ inner ℝ (gradient (K i) x) (gradient φ x)) :=
    integrable_inner_gradient_of_hasCompactSupport hΩ (hK i) hφ hc hs
  have hiR (i : Fin (m + 1)) : Integrable
      (fun x ↦ (deriv f (u x) * v i x ^ 2 - ‖gradient (v i) x‖ ^ 2) * φ x) := by
    have hp : ContinuousOn (gradient (v i)) (epigraph g) :=
      (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
        ((hv i).continuousOn_fderiv_of_isOpen hΩ le_rfl)
    exact integrable_mul_of_tsupport_subset
      ((ha.mul ((hv i).continuousOn.pow 2)).sub (hp.norm.pow 2)) hφ.continuous hc hs
  simp_rw [hpair]
  rw [integral_finsetSum _ (fun i _ ↦ hiL i)]
  simp_rw [show ∀ i, (∫ x, inner ℝ (gradient (K i) x) (gradient φ x)) =
    ∫ x, (deriv f (u x) * v i x ^ 2 - ‖gradient (v i) x‖ ^ 2) * φ x from he]
  rw [← integral_finsetSum _ (fun i _ ↦ hiR i)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ by
    dsimp only
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hsq : (∑ i, v i x ^ 2) = ‖gradient u x‖ ^ 2 := by
      have hh := half_gradient_norm_sq_eq_sum b u x
      rw [← Finset.sum_div] at hh
      linarith
    rw [hsq]
    rfl)

end SerrinEpigraph
