module

public import SerrinEpigraph.GradientExcess
public import SerrinEpigraph.WeakLaplacianCalculus

/-!
# The Bernstein quantity with a continuous weak Laplacian
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter
open scoped Topology Laplacian ContDiff

namespace SerrinEpigraph

/-- The localized kinetic energy plus a multiple of half the squared solution. -/
@[expose] def bernsteinQuantity {d : ℕ} (u η : Space d → ℝ) (A : ℝ) (x : Space d) : ℝ :=
  η x * (‖gradient u x‖ ^ 2 / 2) + A * (u x ^ 2 / 2)

/-- The continuous expression representing the weak Laplacian of the Bernstein quantity. -/
@[expose] def bernsteinSource {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (u : Space d → ℝ) (f : ℝ → ℝ) (η : Space d → ℝ) (A : ℝ) (x : Space d) : ℝ :=
  η x * (hessianSquare b u x - deriv f (u x) * ‖gradient u x‖ ^ 2) +
    (‖gradient u x‖ ^ 2 / 2) * (Δ η) x +
    2 * inner ℝ (gradient η x) (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x) +
    A * (‖gradient u x‖ ^ 2 - u x * f (u x))

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The original solution has a C1 gradient in the open epigraph. -/
theorem Hypotheses.gradient_contDiffOn (h : Hypotheses g u f κ) :
    ContDiffOn ℝ 1 (gradient u) (epigraph g) :=
  (toDual ℝ (Space (m + 1))).symm.contDiff.comp_contDiffOn
    (h.solution_contDiffOn.fderiv_of_isOpen
      (isOpen_epigraph h.graph_contDiff.continuous) (m := 1) (by norm_num))

/-- The Bernstein quantity only needs two derivatives of the original solution. -/
theorem Hypotheses.bernsteinQuantity_contDiffOn (h : Hypotheses g u f κ)
    {η : Space (m + 1) → ℝ} (hη : ContDiff ℝ 2 η) (A : ℝ) :
    ContDiffOn ℝ 1 (bernsteinQuantity u η A) (epigraph g) := by
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  exact ((hη.of_le (by norm_num)).contDiffOn.mul
    ((h.gradient_contDiffOn.norm_sq (𝕜 := ℝ)).div_const 2)).add
      (contDiffOn_const.mul ((hu.pow 2).div_const 2))

/-- All coefficients of the weak Bernstein equation are continuous in the open epigraph. -/
theorem Hypotheses.bernsteinSource_continuousOn (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {η : Space (m + 1) → ℝ} (hη : ContDiff ℝ 2 η) (A : ℝ) :
    ContinuousOn (bernsteinSource b u f η A) (epigraph g) := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu := h.solution_contDiffOn.continuousOn
  have hp := h.gradient_contDiffOn.continuousOn
  have hK : ContDiffOn ℝ 1 (fun x ↦ ‖gradient u x‖ ^ 2 / 2) (epigraph g) :=
    (h.gradient_contDiffOn.norm_sq (𝕜 := ℝ)).div_const 2
  have hKp : ContinuousOn (gradient (fun x ↦ ‖gradient u x‖ ^ 2 / 2)) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      (hK.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hηp : Continuous (gradient η) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp
      ((hη.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).continuous_fderiv one_ne_zero)
  have hF : ContinuousOn (fun x ↦ f (u x)) (epigraph g) :=
    h.reaction_contDiffOn.continuousOn.comp hu (fun x hx ↦ (h.positive x hx).le)
  have ha : ContinuousOn (fun x ↦ deriv f (u x)) (epigraph g) :=
    ((h.reaction_contDiffOn.mono Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl).comp hu h.positive
  exact (((hη.continuous.continuousOn.mul
    ((h.hessianSquare_continuousOn b).sub (ha.mul (hp.norm.pow 2)))).add
      (((hp.norm.pow 2).div_const 2).mul (continuous_laplacian_of_contDiff hη).continuousOn)).add
        (continuousOn_const.mul (hηp.continuousOn.inner hKp))).add
          (continuousOn_const.mul ((hp.norm.pow 2).sub (hu.mul hF)))

/-- The weak Bochner and product identities yield the weak Bernstein equation. -/
theorem Hypotheses.bernstein_weak_laplacian (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {η : Space (m + 1) → ℝ} (hη : ContDiff ℝ 2 η) (A : ℝ) :
    HasWeakLaplacian (epigraph g) (bernsteinQuantity u η A) (bernsteinSource b u f η A) := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hp := h.gradient_contDiffOn.continuousOn
  have hK : ContDiffOn ℝ 1 (fun x ↦ ‖gradient u x‖ ^ 2 / 2) (epigraph g) :=
    (h.gradient_contDiffOn.norm_sq (𝕜 := ℝ)).div_const 2
  have hKp : ContinuousOn (gradient (fun x ↦ ‖gradient u x‖ ^ 2 / 2)) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      (hK.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hF : ContinuousOn (fun x ↦ f (u x)) (epigraph g) :=
    h.reaction_contDiffOn.continuousOn.comp hu.continuousOn (fun x hx ↦ (h.positive x hx).le)
  have ha : ContinuousOn (fun x ↦ deriv f (u x)) (epigraph g) :=
    ((h.reaction_contDiffOn.mono Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl).comp hu.continuousOn h.positive
  have hU : HasWeakLaplacian (epigraph g) u (fun x ↦ -f (u x)) := by
    intro φ hφ hc hs
    rw [h.weak_equation hφ hc hs]
    simp only [neg_mul, integral_neg, neg_neg]
  have hU2 : HasWeakLaplacian (epigraph g) (fun x ↦ u x ^ 2 / 2)
      (fun x ↦ ‖gradient u x‖ ^ 2 - u x * f (u x)) := by
    have hh := (hU.mul hU hΩ hu hu hF.neg hF.neg).const_mul hΩ (hu.mul hu) (1 / 2)
    convert hh using 1
    · funext x; ring
    · funext x
      rw [real_inner_self_eq_norm_sq]
      ring
  have hKB : HasWeakLaplacian (epigraph g) (fun x ↦ ‖gradient u x‖ ^ 2 / 2)
      (fun x ↦ hessianSquare b u x - deriv f (u x) * ‖gradient u x‖ ^ 2) := by
    intro φ hφ hc hs
    rw [h.weak_bochner_identity b hφ hc hs, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by dsimp only; ring)
  have hη1 : ContDiffOn ℝ 1 η (epigraph g) := (hη.of_le (by norm_num)).contDiffOn
  have hηp : ContinuousOn (gradient η) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      (hη1.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hKBc : ContinuousOn
      (fun x ↦ hessianSquare b u x - deriv f (u x) * ‖gradient u x‖ ^ 2) (epigraph g) :=
    (h.hessianSquare_continuousOn b).sub (ha.mul (hp.norm.pow 2))
  have hηK := (hasWeakLaplacian_of_contDiffOn hΩ hη.contDiffOn).mul hKB hΩ hη1 hK
    (continuous_laplacian_of_contDiff hη).continuousOn hKBc
  have hA := hU2.const_mul hΩ ((hu.pow 2).div_const 2) A
  have hsum := hηK.add hA hΩ (hη1.mul hK)
    (contDiffOn_const.mul ((hu.pow 2).div_const 2))
    ((((hK.continuousOn.mul (continuous_laplacian_of_contDiff hη).continuousOn).add
      (hη1.continuousOn.mul hKBc)).add (continuousOn_const.mul (hηp.inner hKp))))
    (continuousOn_const.mul ((hp.norm.pow 2).sub (hu.continuousOn.mul hF)))
  convert hsum using 1
  · rfl
  · funext x
    dsimp only [bernsteinSource]
    ring

end SerrinEpigraph
