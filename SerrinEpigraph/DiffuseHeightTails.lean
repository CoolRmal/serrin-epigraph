module

public import SerrinEpigraph.WeakBochner
public import SerrinEpigraph.DistributionalEquation
public import SerrinEpigraph.DiffuseStressEstimates
public import SerrinEpigraph.HarmonicBadSetEnergy
public import SerrinEpigraph.EquilibriumEstimates
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Stable-well height moments by the weak Bochner inequality (HA5)

This module formalizes `docs/rigidity-proof/harmonic-approximation.md` HA5 for the rescaled
translates `v y = zeroExtension g u (x + R • Q y)` at arbitrary centers `x` (in particular at
free-boundary centers), scales `R > 0` and linear isometries `Q` (the rotated rescalings of
`SerrinEpigraph.DiffuseGoodLayers`; `Q = LinearIsometryEquiv.refl` gives the plain translates),
with `ε = 1 / R` and `ρ = ε |∇v|² = |∇v|² / R`. All constants are independent of `x`, `R`, `Q`.

* HA5.a (weak Bochner inequality, only the `C²` potential is used):
  `Hypotheses.stable_well_caccioppoli` (`c ∫ |∇u|² Ψ² ≤ 2 ∫ |∇u|² |∇Ψ|²` where `f' ≤ -c`) and
  `Hypotheses.stable_well_laplacian_inequality` (`2c ∫ |∇u|² ξ ≤ ∫ |∇u|² Δξ`) in physical
  variables; in diffuse variables `Hypotheses.rescaled_stable_well_caccioppoli`
  (`c R² ∫ ρ Ψ² ≤ 2 ∫ ρ |∇Ψ|²`) and `Hypotheses.rescaled_stable_well_laplacian_inequality`
  (HA5.2, `Δρ ≥ 2 c ε⁻² ρ` in the sense of distributions).
* HA5.b: the abstract band estimate `integral_band_le_of_caccioppoli`;
  `RigidityHypotheses.exists_stable_well_band_estimate`
  (`∫_{v ≥ 1-β} ρ w² ≤ C (G/R)² ∫_{supp w} ρ + C ∫_{1-2β ≤ v < 1-β} ρ w²`) and the total bound
  `RigidityHypotheses.exists_stable_well_total_bound`
  (`∫ ρ w² ≤ C (G/R)² ∫_{supp w} ρ + C ∫_{v < 1-β} ρ w²`).
* HA5.c: `RigidityHypotheses.exists_stable_well_tail_selection`
  (`∫_{v ≥ 1-β/2^N} ρ w² ≤ C (G/R)² ∫_{supp w} ρ + (C/N) ∫_{v ≥ 1-β} ρ w²`), selecting one of
  `N` disjoint dyadic bands.
* Under the sharp all-center energy bound,
  `RigidityHypotheses.exists_stable_well_height_bounds_of_sharp_energy` gives both bounds with
  `∫_{supp w} ρ` replaced by `r^m` for `supp w ⊆ B_r`.
* `heightWeight_props`: the height weight `w = (⟪e, y⟫ - a) η` is `C¹`, compactly supported and
  `|∇w| ≤ 1 + (r + |a|) L`.

Here `w` is any compactly supported `C¹` weight with `|∇w| ≤ G`; the height moments of HA5 are
the case `w = (t - a) η`. The fixed-transition moment bound HA5.1 is not assumed: it is the
integral over `{v < 1 - β}` on the right-hand sides.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

/-! ### HA5.a. Pointwise structure of the Bochner flux -/

/-- The gradient of `|∇u|² / 2` paired with a vector is the sum of the coordinate derivatives
times the pairings of their gradients. -/
theorem inner_gradient_half_norm_sq_eq_sum {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {u : Space d → ℝ} {x : Space d} (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (w : Space d) :
    inner ℝ (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x) w =
      ∑ i, fderiv ℝ u x (b i) * inner ℝ (gradient (fun y ↦ fderiv ℝ u y (b i)) x) w := by
  have hv (i : Fin d) : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y (b i)) x :=
    hu.clm_apply (differentiableAt_const (b i))
  have hK (i : Fin d) : DifferentiableAt ℝ (fun y ↦ (fderiv ℝ u y (b i)) ^ 2 / 2) x :=
    by have := hv i; fun_prop
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (hK i).hasFDerivAt)
  have hfunc : (fun y ↦ ‖gradient u y‖ ^ 2 / 2) =
      fun y ↦ ∑ i, (fderiv ℝ u y (b i)) ^ 2 / 2 := by
    funext y
    exact half_gradient_norm_sq_eq_sum b u y
  have hg : gradient (fun y ↦ ∑ i, (fderiv ℝ u y (b i)) ^ 2 / 2) x =
      ∑ i, gradient (fun y ↦ (fderiv ℝ u y (b i)) ^ 2 / 2) x := by
    simp only [gradient, hsum.fderiv, map_sum]
  rw [hfunc, hg, sum_inner]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [gradient_half_sq_at (hv i), real_inner_smul_left]

/-- **Bochner flux bound**: the pairing of `∇(|∇u|²/2)` with `w` is controlled by
`|∇u|² · |D²u|² · |w|²`, where `|D²u|²` is `hessianSquare`. -/
theorem inner_gradient_half_norm_sq_sq_le {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {u : Space d → ℝ} {x : Space d} (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (w : Space d) :
    (inner ℝ (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x) w) ^ 2 ≤
      ‖gradient u x‖ ^ 2 * hessianSquare b u x * ‖w‖ ^ 2 := by
  rw [inner_gradient_half_norm_sq_eq_sum b hu w]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ fderiv ℝ u x (b i))
    (fun i ↦ inner ℝ (gradient (fun y ↦ fderiv ℝ u y (b i)) x) w)
  have hA : ∑ i, (fderiv ℝ u x (b i)) ^ 2 = ‖gradient u x‖ ^ 2 := by
    have hh := half_gradient_norm_sq_eq_sum b u x
    rw [← Finset.sum_div] at hh
    linarith
  have hB : ∑ i, (inner ℝ (gradient (fun y ↦ fderiv ℝ u y (b i)) x) w) ^ 2 ≤
      hessianSquare b u x * ‖w‖ ^ 2 := by
    unfold hessianSquare
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ ↦ ?_)
    have hi := abs_real_inner_le_norm (gradient (fun y ↦ fderiv ℝ u y (b i)) x) w
    calc (inner ℝ (gradient (fun y ↦ fderiv ℝ u y (b i)) x) w) ^ 2
        = |inner ℝ (gradient (fun y ↦ fderiv ℝ u y (b i)) x) w| ^ 2 := (sq_abs _).symm
      _ ≤ (‖gradient (fun y ↦ fderiv ℝ u y (b i)) x‖ * ‖w‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hi 2
      _ = ‖gradient (fun y ↦ fderiv ℝ u y (b i)) x‖ ^ 2 * ‖w‖ ^ 2 := by ring
  calc _ ≤ (∑ i, (fderiv ℝ u x (b i)) ^ 2) *
        ∑ i, (inner ℝ (gradient (fun y ↦ fderiv ℝ u y (b i)) x) w) ^ 2 := hcs
    _ ≤ ‖gradient u x‖ ^ 2 * (hessianSquare b u x * ‖w‖ ^ 2) := by
        rw [hA]
        exact mul_le_mul_of_nonneg_left hB (sq_nonneg _)
    _ = _ := by ring

/-- The squared Hessian norm is nonnegative. -/
theorem hessianSquare_nonneg {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (u : Space d → ℝ) (x : Space d) : 0 ≤ hessianSquare b u x :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- Young's inequality used to absorb the Bochner flux into the Hessian term. -/
private theorem young_absorb {X Ψ A H B : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hX : X ^ 2 ≤ A * H * B) :
    -(H * Ψ ^ 2 / 2 + 2 * (A * B)) ≤ 2 * Ψ * X := by
  have hP : 0 ≤ H * Ψ ^ 2 := mul_nonneg hH (sq_nonneg _)
  have hQ : 0 ≤ A * B := mul_nonneg hA hB
  have h1 : (2 * Ψ * X) ^ 2 ≤ (H * Ψ ^ 2 / 2 + 2 * (A * B)) ^ 2 := by
    have h2 : (2 * Ψ * X) ^ 2 ≤ 4 * (H * Ψ ^ 2) * (A * B) := by
      have := mul_le_mul_of_nonneg_left hX (sq_nonneg (2 * Ψ))
      nlinarith
    nlinarith [sq_nonneg (H * Ψ ^ 2 / 2 - 2 * (A * B))]
  exact (abs_le_of_sq_le_sq' h1 (by positivity)).1

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- Continuity of the second-order quantities of the solution on its open domain. -/
private theorem Hypotheses.stable_well_continuity (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) :
    ContinuousOn (fun x ↦ ‖gradient u x‖ ^ 2) (epigraph g) ∧
      ContinuousOn (hessianSquare b u) (epigraph g) ∧
      ContinuousOn (fun x ↦ deriv f (u x)) (epigraph g) ∧
      ContDiffOn ℝ 1 (fun y ↦ ‖gradient u y‖ ^ 2 / 2) (epigraph g) := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu2 := h.solution_contDiffOn
  have hgrad1 : ContDiffOn ℝ 1 (gradient u) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.contDiff.comp_contDiffOn
      (hu2.fderiv_of_isOpen hΩ (m := 1) (by norm_num))
  have hv (i : Fin (m + 1)) : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y (b i)) (epigraph g) :=
    (hu2.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).clm_apply contDiffOn_const
  refine ⟨hgrad1.continuousOn.norm.pow 2, ?_, ?_, (hgrad1.norm_sq ℝ).div_const 2⟩
  · change ContinuousOn (fun x ↦ ∑ i, ‖gradient (fun y ↦ fderiv ℝ u y (b i)) x‖ ^ 2) _
    apply continuousOn_finsetSum
    intro i _
    exact ((toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      ((hv i).continuousOn_fderiv_of_isOpen hΩ le_rfl)).norm.pow 2
  · exact ((h.reaction_contDiffOn.mono Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl).comp hu2.continuousOn h.positive

/-- The fderiv of the solution is differentiable at every interior point. -/
private theorem Hypotheses.differentiableAt_fderiv (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) : DifferentiableAt ℝ (fderiv ℝ u) x := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  exact ((h.solution_contDiffOn.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).differentiableOn
    one_ne_zero x hx).differentiableAt (hΩ.mem_nhds hx)

/-- A compactly supported `C¹` function has compactly supported squared gradient norm inside its
topological support. -/
private theorem tsupport_norm_gradient_sq_subset {d : ℕ} (Ψ : Space d → ℝ) :
    tsupport (fun x ↦ ‖gradient Ψ x‖ ^ 2) ⊆ tsupport Ψ := by
  apply closure_minimal _ (isClosed_tsupport Ψ)
  intro x hx
  by_contra hn
  apply hx
  simp [gradient, fderiv_of_notMem_tsupport ℝ hn]

/-- **HA5.a, Caccioppoli form of the weak Bochner inequality.** Where `f' ≤ -c` on the support
of a compactly supported `C¹` test `Ψ` inside the positive phase,
`c ∫ |∇u|² Ψ² ≤ 2 ∫ |∇u|² |∇Ψ|²`. The Hessian term of the Bochner identity absorbs the flux;
only two derivatives of `u` and one of `f` (the `C²` potential) are used. -/
theorem Hypotheses.stable_well_caccioppoli (h : Hypotheses g u f κ) {c : ℝ}
    {Ψ : Space (m + 1) → ℝ} (hΨ : ContDiff ℝ 1 Ψ) (hΨc : HasCompactSupport Ψ)
    (hΨs : tsupport Ψ ⊆ epigraph g) (hf' : ∀ x ∈ tsupport Ψ, deriv f (u x) ≤ -c) :
    c * ∫ x, ‖gradient u x‖ ^ 2 * Ψ x ^ 2 ≤
      2 * ∫ x, ‖gradient u x‖ ^ 2 * ‖gradient Ψ x‖ ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  obtain ⟨hgc, hHc, hfc, hF⟩ := h.stable_well_continuity b
  have hφ : ContDiff ℝ 1 (fun x ↦ Ψ x ^ 2) := hΨ.pow 2
  have hφs' : tsupport (fun x ↦ Ψ x ^ 2) ⊆ tsupport Ψ := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := Ψ) (g := Ψ))
  have hφc : HasCompactSupport (fun x ↦ Ψ x ^ 2) :=
    hΨc.mono' ((subset_tsupport _).trans hφs')
  have hφs : tsupport (fun x ↦ Ψ x ^ 2) ⊆ epigraph g := hφs'.trans hΨs
  have hB := h.weak_bochner_identity b hφ hφc hφs
  have hgΨ : Continuous (fun x ↦ ‖gradient Ψ x‖ ^ 2) :=
    ((toDual ℝ (Space (m + 1))).symm.continuous.comp
      (hΨ.continuous_fderiv one_ne_zero)).norm.pow 2
  have hgΨc : HasCompactSupport (fun x ↦ ‖gradient Ψ x‖ ^ 2) :=
    hΨc.mono' ((subset_tsupport _).trans (tsupport_norm_gradient_sq_subset Ψ))
  have hgΨs : tsupport (fun x ↦ ‖gradient Ψ x‖ ^ 2) ⊆ epigraph g :=
    (tsupport_norm_gradient_sq_subset Ψ).trans hΨs
  have Ia : Integrable (fun x ↦ ‖gradient u x‖ ^ 2 * Ψ x ^ 2) :=
    integrable_mul_of_tsupport_subset hgc hφ.continuous hφc hφs
  have IH : Integrable (fun x ↦ hessianSquare b u x * Ψ x ^ 2) :=
    integrable_mul_of_tsupport_subset hHc hφ.continuous hφc hφs
  have Ig : Integrable (fun x ↦ ‖gradient u x‖ ^ 2 * ‖gradient Ψ x‖ ^ 2) :=
    integrable_mul_of_tsupport_subset hgc hgΨ hgΨc hgΨs
  have Iflux : Integrable (fun x ↦ inner ℝ (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x)
      (gradient (fun x ↦ Ψ x ^ 2) x)) :=
    integrable_inner_gradient_of_hasCompactSupport hΩ hF hφ hφc hφs
  have Irhs : Integrable (fun x ↦ (deriv f (u x) * ‖gradient u x‖ ^ 2 - hessianSquare b u x) *
      Ψ x ^ 2) :=
    integrable_mul_of_tsupport_subset ((hfc.mul hgc).sub hHc) hφ.continuous hφc hφs
  have IH2 : Integrable (fun x ↦ hessianSquare b u x * Ψ x ^ 2 / 2) := IH.div_const 2
  have Ilow : Integrable (fun x ↦ -(hessianSquare b u x * Ψ x ^ 2 / 2 +
      2 * (‖gradient u x‖ ^ 2 * ‖gradient Ψ x‖ ^ 2))) := (IH2.add (Ig.const_mul 2)).neg
  have Iup : Integrable (fun x ↦ -c * (‖gradient u x‖ ^ 2 * Ψ x ^ 2) -
      hessianSquare b u x * Ψ x ^ 2) := (Ia.const_mul (-c)).sub IH
  have P1 : ∀ x, -(hessianSquare b u x * Ψ x ^ 2 / 2 +
      2 * (‖gradient u x‖ ^ 2 * ‖gradient Ψ x‖ ^ 2)) ≤
      inner ℝ (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x) (gradient (fun x ↦ Ψ x ^ 2) x) := by
    intro x
    by_cases hx : x ∈ epigraph g
    · have hgφ : gradient (fun x ↦ Ψ x ^ 2) x = (2 * Ψ x) • gradient Ψ x := by
        have hd := hΨ.differentiable one_ne_zero x
        rw [show (fun x ↦ Ψ x ^ 2) = fun y ↦ Ψ y * Ψ y from funext (fun y ↦ pow_two _),
          gradient_mul_at hd hd, ← add_smul, two_mul]
      rw [hgφ, real_inner_smul_right]
      exact young_absorb (sq_nonneg _) (hessianSquare_nonneg b u x) (sq_nonneg _)
        (inner_gradient_half_norm_sq_sq_le b (h.differentiableAt_fderiv hx) (gradient Ψ x))
    · have hxΨ : x ∉ tsupport Ψ := fun hh ↦ hx (hΨs hh)
      have hxφ : x ∉ tsupport (fun x ↦ Ψ x ^ 2) := fun hh ↦ hxΨ (hφs' hh)
      simp [image_eq_zero_of_notMem_tsupport hxΨ, gradient, fderiv_of_notMem_tsupport ℝ hxΨ,
        fderiv_of_notMem_tsupport ℝ hxφ]
  have P2 : ∀ x, (deriv f (u x) * ‖gradient u x‖ ^ 2 - hessianSquare b u x) * Ψ x ^ 2 ≤
      -c * (‖gradient u x‖ ^ 2 * Ψ x ^ 2) - hessianSquare b u x * Ψ x ^ 2 := by
    intro x
    by_cases hx : x ∈ tsupport Ψ
    · have hA := mul_le_mul_of_nonneg_right (hf' x hx) (sq_nonneg ‖gradient u x‖)
      have hΨ2 := sq_nonneg (Ψ x)
      nlinarith
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have L := integral_mono Ilow Iflux P1
  have U := integral_mono Irhs Iup P2
  rw [hB] at L
  rw [integral_neg, integral_add IH2 (Ig.const_mul 2), integral_div,
    integral_const_mul] at L
  rw [integral_sub (Ia.const_mul (-c)) IH, integral_const_mul] at U
  have hH0 : 0 ≤ ∫ x, hessianSquare b u x * Ψ x ^ 2 :=
    integral_nonneg (fun x ↦ mul_nonneg (hessianSquare_nonneg b u x) (sq_nonneg _))
  linarith

/-- **HA5.a, distributional form** `Δ|∇u|² ≥ 2c|∇u|²` of the weak Bochner inequality where
`f' ≤ -c`: for a nonnegative compactly supported `C²` test `ξ` inside the positive phase,
`2c ∫ |∇u|² ξ ≤ ∫ |∇u|² Δξ`. -/
theorem Hypotheses.stable_well_laplacian_inequality (h : Hypotheses g u f κ) {c : ℝ}
    {ξ : Space (m + 1) → ℝ} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξs : tsupport ξ ⊆ epigraph g) (hξ0 : ∀ x, 0 ≤ ξ x)
    (hf' : ∀ x ∈ tsupport ξ, deriv f (u x) ≤ -c) :
    2 * c * ∫ x, ‖gradient u x‖ ^ 2 * ξ x ≤ ∫ x, ‖gradient u x‖ ^ 2 * (Δ ξ) x := by
  let b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  obtain ⟨hgc, hHc, hfc, hF⟩ := h.stable_well_continuity b
  have hIBP := integral_mul_laplacian_eq_neg_inner_gradient (μ := volume) hΩ hF hξ hξc hξs
  have hB := h.weak_bochner_identity b (hξ.of_le (by norm_num)) hξc hξs
  have hlhs : ∫ x, ‖gradient u x‖ ^ 2 * (Δ ξ) x =
      2 * ∫ x, ‖gradient u x‖ ^ 2 / 2 * (Δ ξ) x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hlhs, hIBP, hB]
  have IA : Integrable (fun x ↦ ‖gradient u x‖ ^ 2 * ξ x) :=
    integrable_mul_of_tsupport_subset hgc hξ.continuous hξc hξs
  have Irhs : Integrable (fun x ↦ (deriv f (u x) * ‖gradient u x‖ ^ 2 - hessianSquare b u x) *
      ξ x) :=
    integrable_mul_of_tsupport_subset ((hfc.mul hgc).sub hHc) hξ.continuous hξc hξs
  have hpt : ∀ x, (deriv f (u x) * ‖gradient u x‖ ^ 2 - hessianSquare b u x) * ξ x ≤
      -c * (‖gradient u x‖ ^ 2 * ξ x) := by
    intro x
    by_cases hx : x ∈ tsupport ξ
    · have hA := mul_le_mul_of_nonneg_right (hf' x hx) (sq_nonneg ‖gradient u x‖)
      have hH := hessianSquare_nonneg b u x
      have hξx := hξ0 x
      nlinarith
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hmono := integral_mono Irhs (IA.const_mul (-c)) hpt
  rw [integral_const_mul] at hmono
  linarith

/-! ### HA5.a in diffuse variables -/

/-- Change of variables for a translated dilation. -/
theorem integral_comp_add_smul_of_pos {d : ℕ} (G : Space d → ℝ) (x : Space d) {R : ℝ}
    (hR : 0 < R) : ∫ y, G (x + R • y) = (R ^ d)⁻¹ * ∫ X, G X := by
  have h1 := Measure.integral_comp_smul (volume : Measure (Space d)) (fun y ↦ G (x + y)) R
  have h2 := integral_add_left_eq_self (μ := (volume : Measure (Space d))) G x
  simp only [finrank_euclideanSpace_fin] at h1
  rw [h1, h2, smul_eq_mul, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR.le d))]

/-- Change of variables for a rotated translated dilation. -/
theorem integral_comp_add_smul_isometry_of_pos {d : ℕ} (G : Space d → ℝ) (x : Space d) {R : ℝ}
    (hR : 0 < R) (Q : Space d ≃ₗᵢ[ℝ] Space d) :
    ∫ y, G (x + R • Q y) = (R ^ d)⁻¹ * ∫ X, G X := by
  rw [← integral_comp_add_smul_of_pos G x hR]
  exact Q.measurePreserving.integral_comp Q.toHomeomorph.measurableEmbedding
    (fun z ↦ G (x + R • z))

/-- The affine homeomorphism `X ↦ Q⁻¹ (R⁻¹ (X - x))` returning to rotated diffuse variables. -/
private def diffuseChart {d : ℕ} (x : Space d) {R : ℝ} (hR : 0 < R)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) : Space d ≃ₜ Space d :=
  ((Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne')).trans
    (Homeomorph.addLeft (-(R⁻¹ • x)))).trans Q.symm.toHomeomorph

private theorem diffuseChart_apply {d : ℕ} (x : Space d) {R : ℝ} (hR : 0 < R)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (X : Space d) :
    diffuseChart x hR Q X = Q.symm (-(R⁻¹ • x) + R⁻¹ • X) := rfl

private theorem diffuseChart_add_smul {d : ℕ} (x : Space d) {R : ℝ} (hR : 0 < R)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (y : Space d) : diffuseChart x hR Q (x + R • Q y) = y := by
  have h1 : -(R⁻¹ • x) + R⁻¹ • (x + R • Q y) = Q y := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    abel
  rw [diffuseChart_apply, h1, LinearIsometryEquiv.symm_apply_apply]

private theorem add_smul_diffuseChart {d : ℕ} (x : Space d) {R : ℝ} (hR : 0 < R)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (X : Space d) : x + R • Q (diffuseChart x hR Q X) = X := by
  rw [diffuseChart_apply, LinearIsometryEquiv.apply_symm_apply, smul_add, smul_neg, smul_smul,
    smul_smul, mul_inv_cancel₀ hR.ne', one_smul, one_smul]
  abel

private theorem diffuseChart_eq_affine {d : ℕ} (x : Space d) {R : ℝ} (hR : 0 < R)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (X : Space d) :
    diffuseChart x hR Q X = Q.symm (-(R⁻¹ • x)) + R⁻¹ • Q.symm X := by
  rw [diffuseChart_apply, map_add, map_smul]

/-- Transfer of a diffuse test to physical variables keeps regularity, compact support and
the support condition. -/
private theorem physical_test_props {d : ℕ} (x : Space d) {R : ℝ} (hR : 0 < R)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) {Ψ : Space d → ℝ} {n : WithTop ℕ∞} (hΨ : ContDiff ℝ n Ψ)
    (hΨc : HasCompactSupport Ψ) :
    ContDiff ℝ n (Ψ ∘ diffuseChart x hR Q) ∧ HasCompactSupport (Ψ ∘ diffuseChart x hR Q) ∧
      ∀ X ∈ tsupport (Ψ ∘ diffuseChart x hR Q), diffuseChart x hR Q X ∈ tsupport Ψ := by
  refine ⟨?_, hΨc.comp_homeomorph _, fun X hX ↦ ?_⟩
  · have he : ContDiff ℝ n (fun X : Space d ↦ Q.symm (-(R⁻¹ • x) + R⁻¹ • X)) :=
      Q.symm.contDiff.comp (contDiff_const.add (contDiff_id.const_smul R⁻¹))
    exact hΨ.comp he
  · rw [tsupport_comp_eq_preimage] at hX
    exact hX

private theorem physical_test_eq {d : ℕ} (x : Space d) {R : ℝ} (hR : 0 < R)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (Ψ : Space d → ℝ) :
    Ψ ∘ diffuseChart x hR Q = fun X ↦ Ψ (Q.symm (-(R⁻¹ • x)) + R⁻¹ • Q.symm X) := by
  funext X
  rw [Function.comp_apply, diffuseChart_eq_affine]

private theorem gradient_physical_test {d : ℕ} (x : Space d) {R : ℝ} (hR : 0 < R)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (Ψ : Space d → ℝ) (X : Space d) :
    gradient (Ψ ∘ diffuseChart x hR Q) X = R⁻¹ • Q (gradient Ψ (diffuseChart x hR Q X)) := by
  rw [physical_test_eq, gradient_comp_translate_dilation_isometry, LinearIsometryEquiv.symm_symm,
    diffuseChart_eq_affine]

/-- **HA5.a in diffuse variables (Caccioppoli form).** For the rescaled translate
`v y = zeroExtension g u (x + R • Q y)` (`Q` a linear isometry), `ρ = |∇v|² / R` and a compactly
supported `C¹` test `Ψ` whose support lies in the positive phase where `f'(v) ≤ -c`,
`c R² ∫ ρ Ψ² ≤ 2 ∫ ρ |∇Ψ|²`, i.e. `c ∫ ρ Ψ² ≤ 2 ε² ∫ ρ |∇Ψ|²` with `ε = 1 / R`. -/
theorem Hypotheses.rescaled_stable_well_caccioppoli (h : Hypotheses g u f κ)
    (x : Space (m + 1)) {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {c : ℝ}
    {Ψ : Space (m + 1) → ℝ} (hΨ : ContDiff ℝ 1 Ψ) (hΨc : HasCompactSupport Ψ)
    (hΨs : ∀ y ∈ tsupport Ψ, x + R • Q y ∈ epigraph g)
    (hf' : ∀ y ∈ tsupport Ψ, deriv f (u (x + R • Q y)) ≤ -c) :
    c * R ^ 2 * ∫ y, ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * Ψ y ^ 2 ≤
      2 * ∫ y, ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R *
        ‖gradient Ψ y‖ ^ 2 := by
  obtain ⟨hΦ1, hΦc, hΦts⟩ := physical_test_props x hR Q hΨ hΨc
  set Φ := Ψ ∘ diffuseChart x hR Q with hΦdef
  have hΦs : tsupport Φ ⊆ epigraph g := fun X hX ↦ by
    have hh := hΨs _ (hΦts X hX)
    rwa [add_smul_diffuseChart] at hh
  have hf'' : ∀ X ∈ tsupport Φ, deriv f (u X) ≤ -c := fun X hX ↦ by
    have hh := hf' _ (hΦts X hX)
    rwa [add_smul_diffuseChart] at hh
  have hcacc := h.stable_well_caccioppoli hΦ1 hΦc hΦs hf''
  set U := zeroExtension g u with hU
  have hc1 : ∀ X, ‖gradient u X‖ ^ 2 * Φ X ^ 2 = ‖gradient U X‖ ^ 2 * Φ X ^ 2 := by
    intro X
    by_cases hX : X ∈ epigraph g
    · rw [hU, h.gradient_zeroExtension hX]
    · have hn : X ∉ tsupport Φ := fun hh ↦ hX (hΦs hh)
      simp [image_eq_zero_of_notMem_tsupport hn]
  have hc2 : ∀ X, ‖gradient u X‖ ^ 2 * ‖gradient Φ X‖ ^ 2 =
      ‖gradient U X‖ ^ 2 * ‖gradient Φ X‖ ^ 2 := by
    intro X
    by_cases hX : X ∈ epigraph g
    · rw [hU, h.gradient_zeroExtension hX]
    · have hn : X ∉ tsupport Φ := fun hh ↦ hX (hΦs hh)
      simp [gradient, fderiv_of_notMem_tsupport ℝ hn]
  simp_rw [hc1, hc2] at hcacc
  have hv : ∀ y, ‖gradient (fun z ↦ U (x + R • Q z)) y‖ = R * ‖gradient U (x + R • Q y)‖ := by
    intro y
    rw [gradient_comp_translate_dilation_isometry, norm_smul, LinearIsometryEquiv.norm_map,
      Real.norm_of_nonneg hR.le]
  set A := ∫ y, ‖gradient (fun z ↦ U (x + R • Q z)) y‖ ^ 2 / R * Ψ y ^ 2 with hA
  set B := ∫ y, ‖gradient (fun z ↦ U (x + R • Q z)) y‖ ^ 2 / R * ‖gradient Ψ y‖ ^ 2 with hB
  have hI1 : ∫ X, ‖gradient U X‖ ^ 2 * Φ X ^ 2 = R ^ (m + 1) * (R⁻¹ * A) := by
    have hcv := integral_comp_add_smul_isometry_of_pos
      (fun X ↦ ‖gradient U X‖ ^ 2 * Φ X ^ 2) x hR Q
    have hpt : ∀ y, ‖gradient U (x + R • Q y)‖ ^ 2 * Φ (x + R • Q y) ^ 2 =
        R⁻¹ * (‖gradient (fun z ↦ U (x + R • Q z)) y‖ ^ 2 / R * Ψ y ^ 2) := by
      intro y
      rw [hv, hΦdef, Function.comp_apply, diffuseChart_add_smul]
      field_simp
    simp_rw [hpt] at hcv
    rw [integral_const_mul] at hcv
    rw [← hA] at hcv
    have hRn : (R ^ (m + 1)) ≠ 0 := pow_ne_zero _ hR.ne'
    field_simp at hcv ⊢
    linarith
  have hI2 : ∫ X, ‖gradient U X‖ ^ 2 * ‖gradient Φ X‖ ^ 2 = R ^ (m + 1) * (R⁻¹ ^ 3 * B) := by
    have hcv := integral_comp_add_smul_isometry_of_pos
      (fun X ↦ ‖gradient U X‖ ^ 2 * ‖gradient Φ X‖ ^ 2) x hR Q
    have hpt : ∀ y, ‖gradient U (x + R • Q y)‖ ^ 2 * ‖gradient Φ (x + R • Q y)‖ ^ 2 =
        R⁻¹ ^ 3 * (‖gradient (fun z ↦ U (x + R • Q z)) y‖ ^ 2 / R * ‖gradient Ψ y‖ ^ 2) := by
      intro y
      rw [hv, hΦdef, gradient_physical_test, diffuseChart_add_smul, norm_smul,
        LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
      field_simp
    simp_rw [hpt] at hcv
    rw [integral_const_mul] at hcv
    rw [← hB] at hcv
    have hRn : (R ^ (m + 1)) ≠ 0 := pow_ne_zero _ hR.ne'
    field_simp at hcv ⊢
    linarith
  rw [hI1, hI2] at hcacc
  have key : (R ^ (m + 1) * R⁻¹ ^ 3) * (c * R ^ 2 * A) ≤ (R ^ (m + 1) * R⁻¹ ^ 3) * (2 * B) := by
    have e1 : (R ^ (m + 1) * R⁻¹ ^ 3) * (c * R ^ 2 * A) = c * (R ^ (m + 1) * (R⁻¹ * A)) := by
      field_simp
    have e2 : (R ^ (m + 1) * R⁻¹ ^ 3) * (2 * B) = 2 * (R ^ (m + 1) * (R⁻¹ ^ 3 * B)) := by ring
    rw [e1, e2]
    exact hcacc
  exact le_of_mul_le_mul_left key (by positivity)

/-- The Laplacian vanishes off the topological support. -/
private theorem laplacian_vanishes_off_tsupport {d : ℕ} (ψ : Space d → ℝ) {y : Space d}
    (hy : y ∉ tsupport ψ) : (Δ ψ) y = 0 := by
  have hz : iteratedFDeriv ℝ 2 ψ y = 0 := Function.notMem_support.mp
    (fun hmem ↦ hy (support_iteratedFDeriv_subset (𝕜 := ℝ) 2 hmem))
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hz,
    zero_apply, Finset.sum_const_zero]

/-- **HA5.a in diffuse variables, distributional form (HA5.2).** For the rescaled translate
`v y = U(x + R • Q y)`, `ρ = |∇v|² / R` and a nonnegative compactly supported `C²` test `ξ` whose
support lies in the positive phase where `f'(v) ≤ -c`: `2 c R² ∫ ρ ξ ≤ ∫ ρ Δξ`, i.e.
`Δρ ≥ 2 c ε⁻² ρ` in the sense of distributions, with `ε = 1 / R`. -/
theorem Hypotheses.rescaled_stable_well_laplacian_inequality (h : Hypotheses g u f κ)
    (x : Space (m + 1)) {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {c : ℝ}
    {ξ : Space (m + 1) → ℝ} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξs : ∀ y ∈ tsupport ξ, x + R • Q y ∈ epigraph g) (hξ0 : ∀ y, 0 ≤ ξ y)
    (hf' : ∀ y ∈ tsupport ξ, deriv f (u (x + R • Q y)) ≤ -c) :
    2 * c * R ^ 2 * ∫ y, ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * ξ y ≤
      ∫ y, ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * (Δ ξ) y := by
  obtain ⟨hΦ2, hΦc, hΦts⟩ := physical_test_props x hR Q hξ hξc
  set Φ := ξ ∘ diffuseChart x hR Q with hΦdef
  have hΦs : tsupport Φ ⊆ epigraph g := fun X hX ↦ by
    have hh := hξs _ (hΦts X hX)
    rwa [add_smul_diffuseChart] at hh
  have hf'' : ∀ X ∈ tsupport Φ, deriv f (u X) ≤ -c := fun X hX ↦ by
    have hh := hf' _ (hΦts X hX)
    rwa [add_smul_diffuseChart] at hh
  have hΦ0 : ∀ X, 0 ≤ Φ X := fun X ↦ hξ0 _
  have hlap := h.stable_well_laplacian_inequality hΦ2 hΦc hΦs hΦ0 hf''
  set U := zeroExtension g u with hU
  have hc1 : ∀ X, ‖gradient u X‖ ^ 2 * Φ X = ‖gradient U X‖ ^ 2 * Φ X := by
    intro X
    by_cases hX : X ∈ epigraph g
    · rw [hU, h.gradient_zeroExtension hX]
    · have hn : X ∉ tsupport Φ := fun hh ↦ hX (hΦs hh)
      simp [image_eq_zero_of_notMem_tsupport hn]
  have hc2 : ∀ X, ‖gradient u X‖ ^ 2 * (Δ Φ) X = ‖gradient U X‖ ^ 2 * (Δ Φ) X := by
    intro X
    by_cases hX : X ∈ epigraph g
    · rw [hU, h.gradient_zeroExtension hX]
    · have hn : X ∉ tsupport Φ := fun hh ↦ hX (hΦs hh)
      rw [laplacian_vanishes_off_tsupport Φ hn, mul_zero, mul_zero]
  simp_rw [hc1, hc2] at hlap
  have hv : ∀ y, ‖gradient (fun z ↦ U (x + R • Q z)) y‖ = R * ‖gradient U (x + R • Q y)‖ := by
    intro y
    rw [gradient_comp_translate_dilation_isometry, norm_smul, LinearIsometryEquiv.norm_map,
      Real.norm_of_nonneg hR.le]
  have hΔΦ : ∀ y, (Δ Φ) (x + R • Q y) = R⁻¹ ^ 2 * (Δ ξ) y := by
    intro y
    have hpt : Q.symm (-(R⁻¹ • x)) + R⁻¹ • Q.symm (x + R • Q y) = y := by
      rw [← diffuseChart_eq_affine x hR Q, diffuseChart_add_smul]
    have hh := laplacian_comp_translate_dilation_isometry_of_contDiffAt (Q.symm (-(R⁻¹ • x)))
      R⁻¹ Q.symm (x + R • Q y) hξ.contDiffAt
    rw [hpt] at hh
    rw [hΦdef, physical_test_eq]
    exact hh
  set A := ∫ y, ‖gradient (fun z ↦ U (x + R • Q z)) y‖ ^ 2 / R * ξ y with hA
  set B := ∫ y, ‖gradient (fun z ↦ U (x + R • Q z)) y‖ ^ 2 / R * (Δ ξ) y with hB
  have hI1 : ∫ X, ‖gradient U X‖ ^ 2 * Φ X = R ^ (m + 1) * (R⁻¹ * A) := by
    have hcv := integral_comp_add_smul_isometry_of_pos
      (fun X ↦ ‖gradient U X‖ ^ 2 * Φ X) x hR Q
    have hpt : ∀ y, ‖gradient U (x + R • Q y)‖ ^ 2 * Φ (x + R • Q y) =
        R⁻¹ * (‖gradient (fun z ↦ U (x + R • Q z)) y‖ ^ 2 / R * ξ y) := by
      intro y
      rw [hv, hΦdef, Function.comp_apply, diffuseChart_add_smul]
      field_simp
    simp_rw [hpt] at hcv
    rw [integral_const_mul] at hcv
    rw [← hA] at hcv
    have hRn : (R ^ (m + 1)) ≠ 0 := pow_ne_zero _ hR.ne'
    field_simp at hcv ⊢
    linarith
  have hI2 : ∫ X, ‖gradient U X‖ ^ 2 * (Δ Φ) X = R ^ (m + 1) * (R⁻¹ ^ 3 * B) := by
    have hcv := integral_comp_add_smul_isometry_of_pos
      (fun X ↦ ‖gradient U X‖ ^ 2 * (Δ Φ) X) x hR Q
    have hpt : ∀ y, ‖gradient U (x + R • Q y)‖ ^ 2 * (Δ Φ) (x + R • Q y) =
        R⁻¹ ^ 3 * (‖gradient (fun z ↦ U (x + R • Q z)) y‖ ^ 2 / R * (Δ ξ) y) := by
      intro y
      rw [hv, hΔΦ]
      field_simp
    simp_rw [hpt] at hcv
    rw [integral_const_mul] at hcv
    rw [← hB] at hcv
    have hRn : (R ^ (m + 1)) ≠ 0 := pow_ne_zero _ hR.ne'
    field_simp at hcv ⊢
    linarith
  rw [hI1, hI2] at hlap
  have key : (R ^ (m + 1) * R⁻¹ ^ 3) * (2 * c * R ^ 2 * A) ≤ (R ^ (m + 1) * R⁻¹ ^ 3) * B := by
    have e1 : (R ^ (m + 1) * R⁻¹ ^ 3) * (2 * c * R ^ 2 * A) =
        2 * c * (R ^ (m + 1) * (R⁻¹ * A)) := by
      field_simp
    have e2 : (R ^ (m + 1) * R⁻¹ ^ 3) * B = R ^ (m + 1) * (R⁻¹ ^ 3 * B) := by ring
    rw [e1, e2]
    exact hlap
  exact le_of_mul_le_mul_left key (by positivity)

/-! ### Stable-well constants and value cutoffs -/

/-- Stable-well constants: a width `b`, a coercivity `c` of `-f'` and a bound `C` with
`W(s) ≤ C (1 - s)²` on `[1 - b, 1]`, where `W = normalizedPotential f`. -/
theorem RigidityHypotheses.exists_stable_well_constants (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ b c C : ℝ, 0 < b ∧ b < 1 ∧ 0 < c ∧ 0 < C ∧
      (∀ s, 1 - b ≤ s → s ≤ 1 → deriv f s ≤ -c) ∧
      (∀ s, 1 - b ≤ s → s ≤ 1 → normalizedPotential f s ≤ C * (1 - s) ^ 2) := by
  obtain ⟨c, δ, hc, hδ, hder⟩ := hr.exists_reaction_deriv_bound h
  obtain ⟨b₂, c₂, C₂, hb₂, hc₂, hcC, hpot⟩ := hr.exists_stable_well_potential_bounds h
  refine ⟨min (δ / 2) b₂, c, C₂ / 2, lt_min (half_pos hδ) hb₂.1,
    (min_le_right _ _).trans_lt hb₂.2, hc, by linarith, ?_, ?_⟩
  · intro s hs1 hs2
    have hb : min (δ / 2) b₂ ≤ δ / 2 := min_le_left _ _
    have habs : |s - 1| < δ := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    linarith [(hder s habs).2]
  · intro s hs1 hs2
    have hb : min (δ / 2) b₂ ≤ b₂ := min_le_right _ _
    exact (hpot s ⟨by linarith, hs2⟩).2.2.2

/-- The derivative of the smooth transition vanishes off `[0, 1]` and is bounded. -/
theorem exists_deriv_smoothTransition_bound :
    ∃ A : ℝ, 0 ≤ A ∧ (∀ t, |deriv Real.smoothTransition t| ≤ A) ∧
      ∀ t, t ∉ Icc (0 : ℝ) 1 → deriv Real.smoothTransition t = 0 := by
  have hzero : ∀ t, t ∉ Icc (0 : ℝ) 1 → deriv Real.smoothTransition t = 0 := by
    intro t ht
    rcases lt_or_ge t 0 with h0 | h0
    · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds h0] with s hs
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
      rw [he.deriv_eq, deriv_const]
    · have h1 : 1 < t := by
        by_contra hn
        exact ht ⟨h0, not_lt.mp hn⟩
      have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds h1] with s hs
        exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
      rw [he.deriv_eq, deriv_const]
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨max A 0, le_max_right _ _, fun t ↦ ?_, hzero⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hAt : |deriv Real.smoothTransition t| ≤ A := by
      simpa only [Real.norm_eq_abs] using hA t ht
    exact hAt.trans (le_max_left _ _)
  · rw [hzero t ht, abs_zero]
    exact le_max_right _ _

/-- The value cutoff `θ_β(s) = smoothTransition ((s - (1 - 2β)) / (β / 2))`: it vanishes for
`s ≤ 1 - 2β`, equals one for `s ≥ 1 - 3β/2`, and its derivative is supported in
`[1 - 2β, 1 - 3β/2]`. -/
def stableWellCutoff (β s : ℝ) : ℝ :=
  Real.smoothTransition ((s - (1 - 2 * β)) / (β / 2))

theorem stableWellCutoff_contDiff {β : ℝ} {n : ℕ∞} : ContDiff ℝ n (stableWellCutoff β) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem stableWellCutoff_of_le {β s : ℝ} (hβ : 0 < β) (hs : s ≤ 1 - 2 * β) :
    stableWellCutoff β s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem stableWellCutoff_of_ge {β s : ℝ} (hβ : 0 < β) (hs : 1 - β ≤ s) :
    stableWellCutoff β s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem stableWellCutoff_mem_Icc (β s : ℝ) : stableWellCutoff β s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem hasDerivAt_stableWellCutoff (β s : ℝ) :
    HasDerivAt (stableWellCutoff β)
      (deriv Real.smoothTransition ((s - (1 - 2 * β)) / (β / 2)) * (1 / (β / 2))) s := by
  have hT := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
    ((s - (1 - 2 * β)) / (β / 2))).hasDerivAt
  have hA : HasDerivAt (fun s : ℝ ↦ (s - (1 - 2 * β)) / (β / 2)) (1 / (β / 2)) s := by
    have h1 := ((hasDerivAt_id' s).sub_const (1 - 2 * β)).div_const (β / 2)
    simpa only [one_div] using h1
  exact hT.comp s hA

/-- Bounds on the derivative of the value cutoff: `|θ_β'| ≤ 2A / β`, and `θ_β'(s) = 0` unless
`1 - 2β ≤ s < 1 - β`. -/
theorem deriv_stableWellCutoff_bound {A : ℝ}
    (hA : ∀ t, |deriv Real.smoothTransition t| ≤ A)
    (hA0 : ∀ t, t ∉ Icc (0 : ℝ) 1 → deriv Real.smoothTransition t = 0) {β : ℝ} (hβ : 0 < β)
    (s : ℝ) :
    |deriv (stableWellCutoff β) s| ≤ 2 * A / β ∧
      (deriv (stableWellCutoff β) s ≠ 0 → 1 - 2 * β ≤ s ∧ s < 1 - β) := by
  rw [(hasDerivAt_stableWellCutoff β s).deriv]
  have hβ2 : 0 < β / 2 := by positivity
  refine ⟨?_, fun hne ↦ ?_⟩
  · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (β / 2))]
    calc |deriv Real.smoothTransition ((s - (1 - 2 * β)) / (β / 2))| * (1 / (β / 2))
        ≤ A * (1 / (β / 2)) := mul_le_mul_of_nonneg_right (hA _) (by positivity)
      _ = 2 * A / β := by field_simp
  · have hmem : (s - (1 - 2 * β)) / (β / 2) ∈ Icc (0 : ℝ) 1 := by
      by_contra hn
      exact hne (by rw [hA0 _ hn, zero_mul])
    rw [mem_Icc, le_div_iff₀ hβ2, div_le_iff₀ hβ2] at hmem
    constructor <;> linarith [hmem.1, hmem.2]

/-! ### Diffuse-variable regularity of the rescaled translates -/

/-- The rescaled translate `y ↦ U(x + R • Q y)` is continuous. -/
theorem Hypotheses.continuous_rescaled_translate (h : Hypotheses g u f κ) (x : Space (m + 1))
    (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) :
    Continuous (fun z ↦ zeroExtension g u (x + R • Q z)) :=
  h.zeroExtension_continuous.comp (continuous_const.add (Q.continuous.const_smul R))

/-- The rescaled translate `y ↦ U(x + R • Q y)` is locally Lipschitz. -/
theorem Hypotheses.locallyLipschitz_rescaled_translate (h : Hypotheses g u f κ)
    (x : Space (m + 1)) (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) :
    LocallyLipschitz (fun z ↦ zeroExtension g u (x + R • Q z)) :=
  locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz x R Q

/-- The rescaled translate is `C²` near every point of its positive phase. -/
theorem Hypotheses.contDiffAt_rescaled (h : Hypotheses g u f κ) (x : Space (m + 1)) (R : ℝ)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {y : Space (m + 1)}
    (hy : x + R • Q y ∈ epigraph g) :
    ContDiffAt ℝ 2 (fun z ↦ zeroExtension g u (x + R • Q z)) y := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hU : ContDiffAt ℝ 2 (zeroExtension g u) (x + R • Q y) :=
    (h.solution_contDiffOn.contDiffAt (hΩ.mem_nhds hy)).congr_of_eventuallyEq
      (zeroExtension_eventuallyEq h.graph_contDiff.continuous hy)
  have haff : ContDiffAt ℝ 2 (fun z : Space (m + 1) ↦ x + R • Q z) y :=
    (contDiff_const.add (Q.contDiff.const_smul R)).contDiffAt
  exact hU.comp y haff

/-- A value cutoff vanishing below a positive level composes to a globally `C¹` function. -/
theorem Hypotheses.contDiff_cutoff_comp_rescaled (h : Hypotheses g u f κ) (x : Space (m + 1))
    (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hθ0 : ∀ s ≤ s₀, θ s = 0) :
    ContDiff ℝ 1 (fun y ↦ θ (zeroExtension g u (x + R • Q y))) := by
  have hcont := h.continuous_rescaled_translate x R Q
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : zeroExtension g u (x + R • Q y) < s₀
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hy)] with z hz
    exact hθ0 _ hz.le
  · have hpos : 0 < zeroExtension g u (x + R • Q y) := lt_of_lt_of_le hs₀ (not_lt.mp hy)
    have hmem := (h.zeroExtension_pos_iff _).mp hpos
    exact hθ.contDiffAt.comp y ((h.contDiffAt_rescaled x R Q hmem).of_le (by norm_num))

/-- Gradient bound for a value cutoff of the rescaled translate. -/
theorem Hypotheses.norm_gradient_cutoff_comp_rescaled_le (h : Hypotheses g u f κ)
    (x : Space (m + 1)) (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ 1 θ) {s₀ : ℝ} (hs₀ : 0 < s₀) (hθ0 : ∀ s ≤ s₀, θ s = 0)
    (y : Space (m + 1)) :
    ‖gradient (fun z ↦ θ (zeroExtension g u (x + R • Q z))) y‖ ≤
      |deriv θ (zeroExtension g u (x + R • Q y))| *
        ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ := by
  have hcont := h.continuous_rescaled_translate x R Q
  by_cases hy : zeroExtension g u (x + R • Q y) < s₀
  · have he : (fun z ↦ θ (zeroExtension g u (x + R • Q z))) =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hy)] with z hz
      exact hθ0 _ hz.le
    have h0 : gradient (fun _ : Space (m + 1) ↦ (0 : ℝ)) y = 0 := by simp [gradient]
    rw [he.gradient_eq, h0, norm_zero]
    positivity
  · have hpos : 0 < zeroExtension g u (x + R • Q y) := lt_of_lt_of_le hs₀ (not_lt.mp hy)
    have hmem := (h.zeroExtension_pos_iff _).mp hpos
    have hv : DifferentiableAt ℝ (fun z ↦ zeroExtension g u (x + R • Q z)) y :=
      (h.contDiffAt_rescaled x R Q hmem).differentiableAt (by norm_num)
    have hθd : HasDerivAt θ (deriv θ (zeroExtension g u (x + R • Q y)))
        (zeroExtension g u (x + R • Q y)) :=
      (hθ.differentiable one_ne_zero _).hasDerivAt
    have hc := hθd.comp_hasFDerivAt y hv.hasFDerivAt
    have hg : gradient (fun z ↦ θ (zeroExtension g u (x + R • Q z))) y =
        deriv θ (zeroExtension g u (x + R • Q y)) •
          gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y := by
      simp only [gradient]
      rw [show (fun z ↦ θ (zeroExtension g u (x + R • Q z))) =
        θ ∘ fun z ↦ zeroExtension g u (x + R • Q z) from rfl, hc.fderiv, map_smul]
    rw [hg, norm_smul, Real.norm_eq_abs]

/-- The rescaled Modica bound `|∇v|² ≤ 2 R² W(v)` on the positive phase of
`v y = U(x + R • Q y)`. -/
theorem RigidityHypotheses.norm_gradient_rescaled_sq_le (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (x : Space (m + 1)) {R : ℝ} (hR : 0 < R)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {y : Space (m + 1)}
    (hy : 0 < zeroExtension g u (x + R • Q y)) :
    ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 ≤
      2 * R ^ 2 * normalizedPotential f (zeroExtension g u (x + R • Q y)) := by
  have hm := hr.rescaled_isometry_modica_bound h x hR Q y
  have hpd : phasePotentialDensity f (fun z ↦ zeroExtension g u (x + R • Q z)) y =
      normalizedPotential f (zeroExtension g u (x + R • Q y)) :=
    Set.indicator_of_mem (s := {z | 0 < zeroExtension g u (x + R • Q z)}) hy _
  rw [hpd] at hm
  have hR2 : 0 < 2 * R := by positivity
  rw [inv_mul_le_iff₀ hR2] at hm
  calc _ ≤ 2 * R * (R * normalizedPotential f (zeroExtension g u (x + R • Q y))) := hm
    _ = _ := by ring

/-! ### HA5.b. The stable-well band estimate -/

/-- Integrability of the diffuse gradient density against bounded measurable weights vanishing
off a compact set. -/
theorem integrable_gradSq_div_mul_of_bounded {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v)
    (R : ℝ) {K : Set (Space d)} (hK : IsCompact K) {F : Space d → ℝ}
    (hFm : AEStronglyMeasurable F volume) (hFK : ∀ y ∉ K, F y = 0) {M : ℝ}
    (hFM : ∀ y, ‖F y‖ ≤ M) :
    Integrable (fun y ↦ ‖gradient v y‖ ^ 2 / R * F y) := by
  have hon : IntegrableOn (fun y ↦ ‖gradient v y‖ ^ 2 / R * F y) K :=
    ((integrableOn_gradient_sq_of_locallyLipschitz hv hK).div_const R).mul_bdd hFm.restrict
      (Eventually.of_forall hFM)
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
  intro y hy
  by_contra hn
  exact hy (by simp [hFK y hn])

/-- **HA5.b, abstract form.** Let `v` be continuous and locally Lipschitz, and suppose the
diffuse Caccioppoli inequality `c R² ∫ ρ Ψ² ≤ 2 ∫ ρ |∇Ψ|²` (`ρ = |∇v|² / R`) holds for all
compactly supported `C¹` tests supported in `{v ≥ 1 - 2β}`, and the Modica band bound
`|∇v|² ≤ K R² β²` holds on the band `{1 - 2β ≤ v < 1 - β}`. Then for every compactly supported
`C¹` weight `w` with `|∇w| ≤ G`,
`∫_{v ≥ 1 - β} ρ w² ≤ (4/c) (G/R)² ∫_{supp w} ρ + (16 A² K / c) ∫_{band} ρ w²`. -/
theorem integral_band_le_of_caccioppoli {d : ℕ} {v : Space d → ℝ} {R c A K β : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hβ : 0 < β) (hK : 0 ≤ K)
    (hvc : Continuous v) (hvL : LocallyLipschitz v)
    (hA : ∀ t, |deriv Real.smoothTransition t| ≤ A)
    (hAz : ∀ t, t ∉ Icc (0 : ℝ) 1 → deriv Real.smoothTransition t = 0)
    (hθv : ContDiff ℝ 1 (fun y ↦ stableWellCutoff β (v y)))
    (hgrad : ∀ y, ‖gradient (fun z ↦ stableWellCutoff β (v z)) y‖ ≤
      |deriv (stableWellCutoff β) (v y)| * ‖gradient v y‖)
    (hmod : ∀ y, 1 - 2 * β ≤ v y → v y < 1 - β → ‖gradient v y‖ ^ 2 ≤ K * R ^ 2 * β ^ 2)
    (hcacc : ∀ Ψ : Space d → ℝ, ContDiff ℝ 1 Ψ → HasCompactSupport Ψ →
      (∀ y ∈ tsupport Ψ, 1 - 2 * β ≤ v y) →
        c * R ^ 2 * ∫ y, ‖gradient v y‖ ^ 2 / R * Ψ y ^ 2 ≤
          2 * ∫ y, ‖gradient v y‖ ^ 2 / R * ‖gradient Ψ y‖ ^ 2)
    {w : Space d → ℝ} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) {G : ℝ}
    (hG : ∀ y, ‖gradient w y‖ ≤ G) :
    (∫ y in {y | 1 - β ≤ v y}, ‖gradient v y‖ ^ 2 / R * w y ^ 2) ≤
      4 / c * (G / R) ^ 2 * (∫ y in tsupport w, ‖gradient v y‖ ^ 2 / R) +
        16 * A ^ 2 * K / c *
          ∫ y in {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β}, ‖gradient v y‖ ^ 2 / R * w y ^ 2 := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hs₀ : ∀ s ≤ 1 - 2 * β, stableWellCutoff β s = 0 := fun s hs ↦
    stableWellCutoff_of_le hβ hs
  set Ψ : Space d → ℝ := fun y ↦ w y * stableWellCutoff β (v y) with hΨdef
  have hΨ : ContDiff ℝ 1 Ψ := hw.mul hθv
  have hΨc : HasCompactSupport Ψ := hwc.mul_right
  have hΨts : ∀ y ∈ tsupport Ψ, 1 - 2 * β ≤ v y := by
    have hsub : Function.support Ψ ⊆ {y | 1 - 2 * β ≤ v y} := by
      intro y hy
      by_contra hn
      apply hy
      have hn' : v y < 1 - 2 * β := lt_of_not_ge hn
      change w y * stableWellCutoff β (v y) = 0
      rw [hs₀ _ hn'.le, mul_zero]
    exact fun y hy ↦ closure_minimal hsub (isClosed_le continuous_const hvc) hy
  have hC := hcacc Ψ hΨ hΨc hΨts
  -- measurability and compact support
  have hKw : IsCompact (tsupport w) := hwc
  have hband : MeasurableSet {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β} :=
    (measurableSet_le measurable_const hvc.measurable).inter
      (measurableSet_lt hvc.measurable measurable_const)
  have hupper : MeasurableSet {y | 1 - β ≤ v y} := measurableSet_le measurable_const hvc.measurable
  have hwK : ∀ y ∉ tsupport w, w y = 0 := fun y hy ↦ image_eq_zero_of_notMem_tsupport hy
  obtain ⟨Mw, hMw⟩ := hwc.exists_bound_of_continuous hw.continuous
  have hΨK : ∀ y ∉ tsupport w, Ψ y = 0 := fun y hy ↦ by
    change w y * stableWellCutoff β (v y) = 0
    rw [hwK y hy, zero_mul]
  have hθb : ∀ s, |stableWellCutoff β s| ≤ 1 := fun s ↦ by
    rw [abs_le]
    constructor <;> linarith [(stableWellCutoff_mem_Icc β s).1, (stableWellCutoff_mem_Icc β s).2]
  have hΨb : ∀ y, ‖Ψ y ^ 2‖ ≤ Mw ^ 2 := by
    intro y
    rw [Real.norm_of_nonneg (sq_nonneg _), hΨdef]
    have h1 : |w y * stableWellCutoff β (v y)| ≤ Mw := by
      rw [abs_mul]
      calc |w y| * |stableWellCutoff β (v y)| ≤ |w y| * 1 :=
            mul_le_mul_of_nonneg_left (hθb _) (abs_nonneg _)
        _ ≤ Mw := by rw [mul_one, ← Real.norm_eq_abs]; exact hMw y
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs] at h2
  have hgΨc : Continuous (gradient Ψ) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hΨ.continuous_fderiv one_ne_zero)
  obtain ⟨MΨ, hMΨ⟩ := (hwc.mul_right (f' := fun y ↦ stableWellCutoff β (v y))).fderiv ℝ
    |>.exists_bound_of_continuous (hΨ.continuous_fderiv one_ne_zero)
  have hgΨK : ∀ y ∉ tsupport w, ‖gradient Ψ y‖ ^ 2 = 0 := by
    intro y hy
    have hy' : y ∉ tsupport Ψ := fun hh ↦ hy (tsupport_mul_subset_left hh)
    simp [gradient, fderiv_of_notMem_tsupport ℝ hy']
  have hgΨb : ∀ y, ‖‖gradient Ψ y‖ ^ 2‖ ≤ MΨ ^ 2 := by
    intro y
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hn : ‖gradient Ψ y‖ = ‖fderiv ℝ Ψ y‖ := by
      simp only [gradient, LinearIsometryEquiv.norm_map]
    rw [hn]
    exact pow_le_pow_left₀ (norm_nonneg _) (hMΨ y) 2
  have IΨ : Integrable (fun y ↦ ‖gradient v y‖ ^ 2 / R * Ψ y ^ 2) :=
    integrable_gradSq_div_mul_of_bounded hvL R hKw
      ((hΨ.continuous.pow 2).aestronglyMeasurable) (fun y hy ↦ by rw [hΨK y hy]; ring) hΨb
  have IgΨ : Integrable (fun y ↦ ‖gradient v y‖ ^ 2 / R * ‖gradient Ψ y‖ ^ 2) :=
    integrable_gradSq_div_mul_of_bounded hvL R hKw
      ((hgΨc.norm.pow 2).aestronglyMeasurable) hgΨK hgΨb
  have IE : Integrable ((tsupport w).indicator (fun y ↦ ‖gradient v y‖ ^ 2 / R)) := by
    rw [integrable_indicator_iff (isClosed_tsupport w).measurableSet]
    exact (integrableOn_gradient_sq_of_locallyLipschitz hvL hKw).div_const R
  have Iw2 : Integrable (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2) :=
    integrable_gradSq_div_mul_of_bounded hvL R hKw ((hw.continuous.pow 2).aestronglyMeasurable)
      (fun y hy ↦ by rw [hwK y hy]; ring) (fun y ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have h2 := pow_le_pow_left₀ (norm_nonneg _) (hMw y) 2
        rwa [Real.norm_eq_abs, sq_abs] at h2)
  have IB : Integrable ({y | 1 - 2 * β ≤ v y ∧ v y < 1 - β}.indicator
      (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2)) :=
    (integrable_indicator_iff hband).2 Iw2.integrableOn
  -- the pointwise bound on `ρ |∇Ψ|²`
  have hpt : ∀ y, ‖gradient v y‖ ^ 2 / R * ‖gradient Ψ y‖ ^ 2 ≤
      2 * G ^ 2 * (tsupport w).indicator (fun y ↦ ‖gradient v y‖ ^ 2 / R) y +
        8 * A ^ 2 * K * R ^ 2 * {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β}.indicator
          (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2) y := by
    intro y
    have hρ : 0 ≤ ‖gradient v y‖ ^ 2 / R := by positivity
    have hgΨy : ‖gradient Ψ y‖ ^ 2 ≤ 2 * ‖gradient w y‖ ^ 2 +
        2 * (w y ^ 2 * ((deriv (stableWellCutoff β) (v y)) ^ 2 * ‖gradient v y‖ ^ 2)) := by
      have hgm : gradient Ψ y = stableWellCutoff β (v y) • gradient w y +
          w y • gradient (fun z ↦ stableWellCutoff β (v z)) y :=
        gradient_mul_at (hw.differentiable one_ne_zero y) (hθv.differentiable one_ne_zero y)
      rw [hgm]
      have h1 : ‖stableWellCutoff β (v y) • gradient w y‖ ≤ ‖gradient w y‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hθb _)
      have h2 : ‖w y • gradient (fun z ↦ stableWellCutoff β (v z)) y‖ ≤
          |w y| * (|deriv (stableWellCutoff β) (v y)| * ‖gradient v y‖) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hgrad y) (abs_nonneg _)
      have h3 := norm_add_le (stableWellCutoff β (v y) • gradient w y)
        (w y • gradient (fun z ↦ stableWellCutoff β (v z)) y)
      have hP : 0 ≤ ‖stableWellCutoff β (v y) • gradient w y‖ := norm_nonneg _
      have hQ : 0 ≤ ‖w y • gradient (fun z ↦ stableWellCutoff β (v z)) y‖ := norm_nonneg _
      have hsq := pow_le_pow_left₀ (norm_nonneg _) (h3.trans (add_le_add h1 h2)) 2
      have hW : (|w y| * (|deriv (stableWellCutoff β) (v y)| * ‖gradient v y‖)) ^ 2 =
          w y ^ 2 * ((deriv (stableWellCutoff β) (v y)) ^ 2 * ‖gradient v y‖ ^ 2) := by
        rw [mul_pow, mul_pow, sq_abs, sq_abs]
      nlinarith [sq_nonneg (‖gradient w y‖ - |w y| * (|deriv (stableWellCutoff β) (v y)| *
        ‖gradient v y‖)), norm_nonneg (gradient w y),
        mul_nonneg (abs_nonneg (w y)) (mul_nonneg (abs_nonneg
          (deriv (stableWellCutoff β) (v y))) (norm_nonneg (gradient v y)))]
    have hT1 : ‖gradient v y‖ ^ 2 / R * ‖gradient w y‖ ^ 2 ≤
        G ^ 2 * (tsupport w).indicator (fun y ↦ ‖gradient v y‖ ^ 2 / R) y := by
      by_cases hy : y ∈ tsupport w
      · rw [indicator_of_mem hy, mul_comm (G ^ 2)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hG y) 2) hρ
      · have h0 : gradient w y = 0 := by simp [gradient, fderiv_of_notMem_tsupport ℝ hy]
        rw [h0, norm_zero, indicator_of_notMem hy]
        simp
    have hT2 : ‖gradient v y‖ ^ 2 / R *
        (w y ^ 2 * ((deriv (stableWellCutoff β) (v y)) ^ 2 * ‖gradient v y‖ ^ 2)) ≤
        4 * A ^ 2 * K * R ^ 2 * {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β}.indicator
          (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2) y := by
      obtain ⟨hdb, hdsupp⟩ := deriv_stableWellCutoff_bound hA hAz hβ (v y)
      by_cases hne : deriv (stableWellCutoff β) (v y) = 0
      · rw [hne]
        have hind : 0 ≤ {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β}.indicator
            (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2) y :=
          indicator_nonneg (fun z _ ↦ by positivity) y
        have : 0 ≤ 4 * A ^ 2 * K * R ^ 2 := by positivity
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero]
        positivity
      · obtain ⟨hb1, hb2⟩ := hdsupp hne
        have hy : y ∈ {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β} := ⟨hb1, hb2⟩
        rw [indicator_of_mem hy]
        have hdsq : (deriv (stableWellCutoff β) (v y)) ^ 2 ≤ (2 * A / β) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hdb 2
        have hm := hmod y hb1 hb2
        have hprod : (deriv (stableWellCutoff β) (v y)) ^ 2 * ‖gradient v y‖ ^ 2 ≤
            4 * A ^ 2 * K * R ^ 2 := by
          calc _ ≤ (2 * A / β) ^ 2 * (K * R ^ 2 * β ^ 2) :=
                mul_le_mul hdsq hm (sq_nonneg _) (sq_nonneg _)
            _ = 4 * A ^ 2 * K * R ^ 2 := by field_simp; ring
        have hw2 := sq_nonneg (w y)
        calc ‖gradient v y‖ ^ 2 / R *
              (w y ^ 2 * ((deriv (stableWellCutoff β) (v y)) ^ 2 * ‖gradient v y‖ ^ 2))
            ≤ ‖gradient v y‖ ^ 2 / R * (w y ^ 2 * (4 * A ^ 2 * K * R ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hw2) hρ
          _ = 4 * A ^ 2 * K * R ^ 2 * (‖gradient v y‖ ^ 2 / R * w y ^ 2) := by ring
    calc ‖gradient v y‖ ^ 2 / R * ‖gradient Ψ y‖ ^ 2
        ≤ ‖gradient v y‖ ^ 2 / R * (2 * ‖gradient w y‖ ^ 2 +
          2 * (w y ^ 2 * ((deriv (stableWellCutoff β) (v y)) ^ 2 * ‖gradient v y‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hgΨy hρ
      _ = 2 * (‖gradient v y‖ ^ 2 / R * ‖gradient w y‖ ^ 2) + 2 * (‖gradient v y‖ ^ 2 / R *
          (w y ^ 2 * ((deriv (stableWellCutoff β) (v y)) ^ 2 * ‖gradient v y‖ ^ 2))) := by ring
      _ ≤ _ := by linarith [hT1, hT2]
  have hint : ∫ y, ‖gradient v y‖ ^ 2 / R * ‖gradient Ψ y‖ ^ 2 ≤
      ∫ y, (2 * G ^ 2 * (tsupport w).indicator (fun y ↦ ‖gradient v y‖ ^ 2 / R) y +
        8 * A ^ 2 * K * R ^ 2 * {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β}.indicator
          (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2) y) :=
    integral_mono IgΨ ((IE.const_mul (2 * G ^ 2)).add (IB.const_mul
      (8 * A ^ 2 * K * R ^ 2))) hpt
  rw [integral_add (IE.const_mul _) (IB.const_mul _), integral_const_mul, integral_const_mul,
    integral_indicator (isClosed_tsupport w).measurableSet, integral_indicator hband] at hint
  -- the left side
  have hleft : (∫ y in {y | 1 - β ≤ v y}, ‖gradient v y‖ ^ 2 / R * w y ^ 2) ≤
      ∫ y, ‖gradient v y‖ ^ 2 / R * Ψ y ^ 2 := by
    have heq : (∫ y in {y | 1 - β ≤ v y}, ‖gradient v y‖ ^ 2 / R * w y ^ 2) =
        ∫ y in {y | 1 - β ≤ v y}, ‖gradient v y‖ ^ 2 / R * Ψ y ^ 2 := by
      apply setIntegral_congr_fun hupper
      intro y hy
      change ‖gradient v y‖ ^ 2 / R * w y ^ 2 =
        ‖gradient v y‖ ^ 2 / R * (w y * stableWellCutoff β (v y)) ^ 2
      rw [stableWellCutoff_of_ge hβ hy, mul_one]
    rw [heq]
    exact setIntegral_le_integral IΨ (Eventually.of_forall (fun y ↦ by positivity))
  set E := ∫ y in tsupport w, ‖gradient v y‖ ^ 2 / R
  set Bd := ∫ y in {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β}, ‖gradient v y‖ ^ 2 / R * w y ^ 2
  set IP := ∫ y, ‖gradient v y‖ ^ 2 / R * Ψ y ^ 2
  have hcR : 0 < c * R ^ 2 := by positivity
  have key : c * R ^ 2 * IP ≤ c * R ^ 2 *
      (4 / c * (G / R) ^ 2 * E + 16 * A ^ 2 * K / c * Bd) := by
    calc c * R ^ 2 * IP ≤ 2 * ∫ y, ‖gradient v y‖ ^ 2 / R * ‖gradient Ψ y‖ ^ 2 := hC
      _ ≤ 2 * (2 * G ^ 2 * E + 8 * A ^ 2 * K * R ^ 2 * Bd) := by linarith
      _ = c * R ^ 2 * (4 / c * (G / R) ^ 2 * E + 16 * A ^ 2 * K / c * Bd) := by
          field_simp
          ring
  exact hleft.trans (le_of_mul_le_mul_left key hcR)

/-- Integrability of `ρ w²` for a continuous compactly supported weight `w`. -/
theorem integrable_gradSq_div_mul_sq {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v)
    (R : ℝ) {w : Space d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) :
    Integrable (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2) := by
  obtain ⟨M, hM⟩ := hwc.exists_bound_of_continuous hw
  refine integrable_gradSq_div_mul_of_bounded hv R (K := tsupport w) (M := M ^ 2) hwc
    ((hw.pow 2).aestronglyMeasurable) (fun y hy ↦ ?_) (fun y ↦ ?_)
  · rw [image_eq_zero_of_notMem_tsupport hy]
    ring
  · rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hM y) 2
    rwa [Real.norm_eq_abs, sq_abs] at h2

/-- **HA5.b, band estimate for the rescaled translates.** There are a stable-well width `b` and
a constant `C`, independent of the center `x` and of the scale `R`, such that for `0 < β`,
`2β ≤ b` and every compactly supported `C¹` weight `w` with `|∇w| ≤ G`, the rescaled translate
`v y = U(x + R • Q y)` and `ρ = |∇v|² / R` (`ε = 1 / R`) satisfy
`∫_{v ≥ 1 - β} ρ w² ≤ C (G/R)² ∫_{supp w} ρ + C ∫_{1 - 2β ≤ v < 1 - β} ρ w²`. -/
theorem RigidityHypotheses.exists_stable_well_band_estimate (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ b C : ℝ, 0 < b ∧ b < 1 ∧ 0 < C ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ β : ℝ, 0 < β → 2 * β ≤ b →
        ∀ w : Space (m + 1) → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
          ∀ G : ℝ, (∀ y, ‖gradient w y‖ ≤ G) →
            (∫ y in {y | 1 - β ≤ zeroExtension g u (x + R • Q y)},
                ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * w y ^ 2) ≤
              C * (G / R) ^ 2 * (∫ y in tsupport w,
                  ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R) +
                C * ∫ y in {y | 1 - 2 * β ≤ zeroExtension g u (x + R • Q y) ∧
                    zeroExtension g u (x + R • Q y) < 1 - β},
                  ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * w y ^ 2 := by
  obtain ⟨b, c, CW, hb, hb1, hc, hCW, hder, hpot⟩ := hr.exists_stable_well_constants h
  obtain ⟨A, hA0, hA, hAz⟩ := exists_deriv_smoothTransition_bound
  refine ⟨b, 4 / c + 16 * A ^ 2 * (8 * CW) / c, hb, hb1, by positivity, ?_⟩
  intro x R hR Q β hβ hβb w hw hwc G hG
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • Q z) with hvdef
  have hs₀ : 0 < 1 - 2 * β := by linarith
  have hθ0 : ∀ s ≤ 1 - 2 * β, stableWellCutoff β s = 0 := fun s hs ↦
    stableWellCutoff_of_le hβ hs
  have hmod : ∀ y, 1 - 2 * β ≤ v y → v y < 1 - β →
      ‖gradient v y‖ ^ 2 ≤ 8 * CW * R ^ 2 * β ^ 2 := by
    intro y h1 h2
    have hpos : 0 < v y := lt_of_lt_of_le hs₀ h1
    have hm := hr.norm_gradient_rescaled_sq_le h x hR Q hpos
    have hW := hpot (v y) (by linarith) (by linarith)
    have hsq : (1 - v y) ^ 2 ≤ (2 * β) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc ‖gradient v y‖ ^ 2 ≤ 2 * R ^ 2 * normalizedPotential f (v y) := hm
      _ ≤ 2 * R ^ 2 * (CW * (2 * β) ^ 2) := by
          apply mul_le_mul_of_nonneg_left (hW.trans (mul_le_mul_of_nonneg_left hsq hCW.le))
          positivity
      _ = 8 * CW * R ^ 2 * β ^ 2 := by ring
  have hcacc : ∀ Ψ : Space (m + 1) → ℝ, ContDiff ℝ 1 Ψ → HasCompactSupport Ψ →
      (∀ y ∈ tsupport Ψ, 1 - 2 * β ≤ v y) →
        c * R ^ 2 * ∫ y, ‖gradient v y‖ ^ 2 / R * Ψ y ^ 2 ≤
          2 * ∫ y, ‖gradient v y‖ ^ 2 / R * ‖gradient Ψ y‖ ^ 2 := by
    intro Ψ hΨ hΨc hΨs
    have hmem : ∀ y ∈ tsupport Ψ, x + R • Q y ∈ epigraph g := fun y hy ↦
      (h.zeroExtension_pos_iff _).mp (lt_of_lt_of_le hs₀ (hΨs y hy))
    refine h.rescaled_stable_well_caccioppoli x hR Q hΨ hΨc hmem (fun y hy ↦ ?_)
    have hval : u (x + R • Q y) = v y := (zeroExtension_of_mem (hmem y hy)).symm
    rw [hval]
    exact hder _ (by linarith [hΨs y hy]) (hr.zeroExtension_lt_one _).le
  have hmain := integral_band_le_of_caccioppoli (v := v) hR hc hβ
    (by positivity : (0 : ℝ) ≤ 8 * CW) (h.continuous_rescaled_translate x R Q)
    (h.locallyLipschitz_rescaled_translate x R Q) hA hAz
    (h.contDiff_cutoff_comp_rescaled x R Q stableWellCutoff_contDiff hs₀ hθ0)
    (h.norm_gradient_cutoff_comp_rescaled_le x R Q stableWellCutoff_contDiff hs₀ hθ0)
    hmod hcacc hw hwc hG
  have hE : 0 ≤ ∫ y in tsupport w, ‖gradient v y‖ ^ 2 / R :=
    integral_nonneg (fun y ↦ by positivity)
  have hBd : 0 ≤ ∫ y in {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β},
      ‖gradient v y‖ ^ 2 / R * w y ^ 2 := integral_nonneg (fun y ↦ by positivity)
  have h1 : 0 ≤ 16 * A ^ 2 * (8 * CW) / c := by positivity
  have h2 : 0 ≤ 4 / c := by positivity
  refine hmain.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h1) (sq_nonneg _)) hE
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h2) hBd

/-- **HA5.b, total bound.** With constants independent of `x` and `R`, the full weighted
gradient mass is controlled by the part below the stable well:
`∫ ρ w² ≤ C (G/R)² ∫_{supp w} ρ + C ∫_{v < 1 - β} ρ w²`.  Applied with `w = (t - a) η`, this
turns the fixed-transition height-moment bound (HA5.1) into the total height-moment bound. -/
theorem RigidityHypotheses.exists_stable_well_total_bound (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ b C : ℝ, 0 < b ∧ b < 1 ∧ 0 < C ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ β : ℝ, 0 < β → 2 * β ≤ b →
        ∀ w : Space (m + 1) → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
          ∀ G : ℝ, (∀ y, ‖gradient w y‖ ≤ G) →
            (∫ y, ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * w y ^ 2) ≤
              C * (G / R) ^ 2 * (∫ y in tsupport w,
                  ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R) +
                C * ∫ y in {y | zeroExtension g u (x + R • Q y) < 1 - β},
                  ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * w y ^ 2 := by
  obtain ⟨b, C, hb, hb1, hC, hband⟩ := hr.exists_stable_well_band_estimate h
  refine ⟨b, 1 + C, hb, hb1, by positivity, ?_⟩
  intro x R hR Q β hβ hβb w hw hwc G hG
  have hmain := hband x R hR Q β hβ hβb w hw hwc G hG
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • Q z) with hvdef
  have hvc : Continuous v := h.continuous_rescaled_translate x R Q
  have Iw2 : Integrable (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2) :=
    integrable_gradSq_div_mul_sq (h.locallyLipschitz_rescaled_translate x R Q) R hw.continuous hwc
  have hsplit := integral_add_compl (s := {y | v y < 1 - β})
    (measurableSet_lt hvc.measurable measurable_const) Iw2
  have hcompl : {y | v y < 1 - β}ᶜ = {y | 1 - β ≤ v y} := by
    ext y
    simp [not_lt]
  rw [hcompl] at hsplit
  have hBsub : (∫ y in {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β}, ‖gradient v y‖ ^ 2 / R * w y ^ 2) ≤
      ∫ y in {y | v y < 1 - β}, ‖gradient v y‖ ^ 2 / R * w y ^ 2 :=
    setIntegral_mono_set Iw2.integrableOn
      (Eventually.of_forall (fun y ↦ by simp only [Pi.zero_apply]; positivity))
      (show {y | 1 - 2 * β ≤ v y ∧ v y < 1 - β} ⊆ {y | v y < 1 - β} from
        fun y hy ↦ hy.2).eventuallyLE
  set E := ∫ y in tsupport w, ‖gradient v y‖ ^ 2 / R
  set L := ∫ y in {y | v y < 1 - β}, ‖gradient v y‖ ^ 2 / R * w y ^ 2
  have hE : 0 ≤ E := integral_nonneg (fun y ↦ by positivity)
  have hp : 0 ≤ (G / R) ^ 2 * E := mul_nonneg (sq_nonneg _) hE
  have hCB := mul_le_mul_of_nonneg_left hBsub hC.le
  calc (∫ y, ‖gradient v y‖ ^ 2 / R * w y ^ 2)
      = L + ∫ y in {y | 1 - β ≤ v y}, ‖gradient v y‖ ^ 2 / R * w y ^ 2 := hsplit.symm
    _ ≤ L + (C * (G / R) ^ 2 * E + C * L) := by linarith
    _ = C * ((G / R) ^ 2 * E) + (1 + C) * L := by ring
    _ ≤ (1 + C) * ((G / R) ^ 2 * E) + (1 + C) * L := by
        have := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one :
          C ≤ 1 + C) hp
        linarith
    _ = (1 + C) * (G / R) ^ 2 * E + (1 + C) * L := by ring

/-- `2 β / 2^(k+1) = β / 2^k`. -/
private theorem two_mul_div_two_pow_succ (β : ℝ) (k : ℕ) :
    2 * (β / 2 ^ (k + 1)) = β / 2 ^ k := by
  rw [pow_succ]
  field_simp

/-- `β / 2^l ≤ β / 2^j` for `j ≤ l` and `β ≥ 0`. -/
private theorem div_two_pow_anti {β : ℝ} (hβ : 0 ≤ β) {j l : ℕ} (hjl : j ≤ l) :
    β / 2 ^ l ≤ β / 2 ^ j :=
  div_le_div_of_nonneg_left hβ (by positivity) (pow_le_pow_right₀ (by norm_num) hjl)

/-- **HA5.c, finite band selection.** With constants independent of `x`, `R` and `N`: for
`0 < β ≤ b`, every `N ≥ 1` and every compactly supported `C¹` weight `w` with `|∇w| ≤ G`,
`∫_{v ≥ 1 - β / 2^N} ρ w² ≤ C (G/R)² ∫_{supp w} ρ + (C / N) ∫_{v ≥ 1 - β} ρ w²`.
The proof selects, among the `N` disjoint dyadic bands `1 - β / 2^k ≤ v < 1 - β / 2^(k+1)`,
one carrying at most a `1/N` share of the stable-well mass, and applies the band estimate
there. -/
theorem RigidityHypotheses.exists_stable_well_tail_selection (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ b C : ℝ, 0 < b ∧ b < 1 ∧ 0 < C ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ β : ℝ, 0 < β → β ≤ b → ∀ N : ℕ, 0 < N →
        ∀ w : Space (m + 1) → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
          ∀ G : ℝ, (∀ y, ‖gradient w y‖ ≤ G) →
            (∫ y in {y | 1 - β / 2 ^ N ≤ zeroExtension g u (x + R • Q y)},
                ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * w y ^ 2) ≤
              C * (G / R) ^ 2 * (∫ y in tsupport w,
                  ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R) +
                C / N * ∫ y in {y | 1 - β ≤ zeroExtension g u (x + R • Q y)},
                  ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * w y ^ 2 := by
  obtain ⟨b, C, hb, hb1, hC, hband⟩ := hr.exists_stable_well_band_estimate h
  refine ⟨b, C, hb, hb1, hC, ?_⟩
  intro x R hR Q β hβ hβb N hN w hw hwc G hG
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • Q z) with hvdef
  have hvc : Continuous v := h.continuous_rescaled_translate x R Q
  have IF : Integrable (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2) :=
    integrable_gradSq_div_mul_sq (h.locallyLipschitz_rescaled_translate x R Q) R hw.continuous hwc
  have hF0 : 0 ≤ᵐ[volume.restrict {y | 1 - β ≤ v y}]
      (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2) :=
    Eventually.of_forall (fun y ↦ by simp only [Pi.zero_apply]; positivity)
  set B : ℕ → Set (Space (m + 1)) := fun k ↦
    {y | 1 - 2 * (β / 2 ^ (k + 1)) ≤ v y ∧ v y < 1 - β / 2 ^ (k + 1)} with hBdef
  have hBm : ∀ k, MeasurableSet (B k) := fun k ↦
    (measurableSet_le measurable_const hvc.measurable).inter
      (measurableSet_lt hvc.measurable measurable_const)
  have hdisj_lt : ∀ k l : ℕ, k < l → Disjoint (B k) (B l) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro y hyk hyl
    have h1 : v y < 1 - β / 2 ^ (k + 1) := hyk.2
    have h2 : 1 - 2 * (β / 2 ^ (l + 1)) ≤ v y := hyl.1
    rw [two_mul_div_two_pow_succ] at h2
    have h3 := div_two_pow_anti hβ.le (show k + 1 ≤ l from hkl)
    linarith
  have hdisj : Set.Pairwise (↑(Finset.range N)) (Function.onFun Disjoint B) := by
    intro k _ l _ hkl
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · exact hdisj_lt k l hlt
    · exact (hdisj_lt l k hgt).symm
  have hUsub : (⋃ k ∈ Finset.range N, B k) ⊆ {y | 1 - β ≤ v y} := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨k, _, hyk⟩ := hy
    have h1 : 1 - 2 * (β / 2 ^ (k + 1)) ≤ v y := hyk.1
    rw [two_mul_div_two_pow_succ] at h1
    have h2 : β / 2 ^ k ≤ β / 2 ^ 0 := div_two_pow_anti hβ.le (Nat.zero_le k)
    simp only [pow_zero, div_one] at h2
    change 1 - β ≤ v y
    linarith
  set T := ∫ y in {y | 1 - β ≤ v y}, ‖gradient v y‖ ^ 2 / R * w y ^ 2 with hTdef
  have hsum : ∑ k ∈ Finset.range N, (∫ y in B k, ‖gradient v y‖ ^ 2 / R * w y ^ 2) ≤ T := by
    rw [← integral_biUnion_finset (Finset.range N) (fun k _ ↦ hBm k) hdisj
      (fun k _ ↦ IF.integrableOn)]
    exact setIntegral_mono_set IF.integrableOn hF0 hUsub.eventuallyLE
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  obtain ⟨k, hk, hkle⟩ : ∃ k ∈ Finset.range N,
      (∫ y in B k, ‖gradient v y‖ ^ 2 / R * w y ^ 2) ≤ T / N := by
    apply Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr hN.ne')
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hNT : (N : ℝ) * (T / N) = T := by field_simp
    rw [hNT]
    exact hsum
  have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
  have hβk : 0 < β / 2 ^ (k + 1) := by positivity
  have h2βk : 2 * (β / 2 ^ (k + 1)) ≤ b := by
    rw [two_mul_div_two_pow_succ]
    have h2 : β / 2 ^ k ≤ β / 2 ^ 0 := div_two_pow_anti hβ.le (Nat.zero_le k)
    simp only [pow_zero, div_one] at h2
    linarith
  have hmain := hband x R hR Q (β / 2 ^ (k + 1)) hβk h2βk w hw hwc G hG
  have htail : (∫ y in {y | 1 - β / 2 ^ N ≤ v y}, ‖gradient v y‖ ^ 2 / R * w y ^ 2) ≤
      ∫ y in {y | 1 - β / 2 ^ (k + 1) ≤ v y}, ‖gradient v y‖ ^ 2 / R * w y ^ 2 := by
    refine setIntegral_mono_set IF.integrableOn
      (Eventually.of_forall (fun y ↦ by simp only [Pi.zero_apply]; positivity)) ?_
    refine (show {y | 1 - β / 2 ^ N ≤ v y} ⊆ {y | 1 - β / 2 ^ (k + 1) ≤ v y} from ?_).eventuallyLE
    intro y hy
    have h3 := div_two_pow_anti hβ.le hkN
    change 1 - β / 2 ^ (k + 1) ≤ v y
    have hy' : 1 - β / 2 ^ N ≤ v y := hy
    linarith
  set E := ∫ y in tsupport w, ‖gradient v y‖ ^ 2 / R
  have hCk := mul_le_mul_of_nonneg_left hkle hC.le
  calc (∫ y in {y | 1 - β / 2 ^ N ≤ v y}, ‖gradient v y‖ ^ 2 / R * w y ^ 2)
      ≤ C * (G / R) ^ 2 * E + C * ∫ y in B k, ‖gradient v y‖ ^ 2 / R * w y ^ 2 :=
        htail.trans hmain
    _ ≤ C * (G / R) ^ 2 * E + C * (T / N) := by linarith
    _ = C * (G / R) ^ 2 * E + C / N * T := by ring

/-! ### Height weights -/

/-- The gradient of an affine height function `y ↦ ⟪e, y⟫ - a` is `e`. -/
theorem gradient_inner_sub_const {d : ℕ} (e : Space d) (a : ℝ) (y : Space d) :
    gradient (fun z ↦ inner ℝ e z - a) y = e := by
  have hd : HasFDerivAt (fun z : Space d ↦ inner ℝ e z - a)
      (toDual ℝ (Space d) e : StrongDual ℝ (Space d)) y := by
    have h1 := ((toDual ℝ (Space d) e : StrongDual ℝ (Space d)).hasFDerivAt (x := y)).sub_const a
    simpa only [InnerProductSpace.toDual_apply_apply] using h1
  simp only [gradient, hd.fderiv, LinearIsometryEquiv.symm_apply_apply]

/-- The height weight `w(y) = (⟪e, y⟫ - a) η(y)` of HA5.b: for a `C¹` cutoff `η` with
`|η| ≤ 1`, `|∇η| ≤ L` and support in `closedBall 0 r`, and `‖e‖ ≤ 1`, the weight is `C¹`, compactly
supported inside `tsupport η`, and `|∇w| ≤ 1 + (r + |a|) L`. -/
theorem heightWeight_props {d : ℕ} {e : Space d} (he : ‖e‖ ≤ 1) (a : ℝ) {η : Space d → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) {r L : ℝ} (hr : 0 ≤ r)
    (hηs : tsupport η ⊆ closedBall 0 r) (hη1 : ∀ y, |η y| ≤ 1)
    (hηL : ∀ y, ‖gradient η y‖ ≤ L) :
    ContDiff ℝ 1 (fun y ↦ (inner ℝ e y - a) * η y) ∧
      HasCompactSupport (fun y ↦ (inner ℝ e y - a) * η y) ∧
      tsupport (fun y ↦ (inner ℝ e y - a) * η y) ⊆ tsupport η ∧
      ∀ y, ‖gradient (fun y ↦ (inner ℝ e y - a) * η y) y‖ ≤ 1 + (r + |a|) * L := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hηL 0)
  have hlin : ContDiff ℝ 1 (fun z : Space d ↦ inner ℝ e z - a) := by
    have h1 := (toDual ℝ (Space d) e : StrongDual ℝ (Space d)).contDiff (n := 1)
    have h2 : (fun z : Space d ↦ inner ℝ e z - a) =
        fun z ↦ (toDual ℝ (Space d) e : StrongDual ℝ (Space d)) z - a := by
      funext z
      rw [InnerProductSpace.toDual_apply_apply]
    rw [h2]
    exact h1.sub contDiff_const
  refine ⟨hlin.mul hη, hηc.mul_left, tsupport_mul_subset_right, fun y ↦ ?_⟩
  rw [gradient_mul_at (hlin.differentiable one_ne_zero y) (hη.differentiable one_ne_zero y),
    gradient_inner_sub_const]
  by_cases hy : y ∈ tsupport η
  · have hyr : ‖y‖ ≤ r := by simpa using hηs hy
    have hin : |inner ℝ e y - a| ≤ r + |a| := by
      have h1 : |inner ℝ e y| ≤ r := (abs_real_inner_le_norm e y).trans
        ((mul_le_mul he hyr (norm_nonneg _) zero_le_one).trans_eq (one_mul r))
      calc |inner ℝ e y - a| ≤ |inner ℝ e y| + |a| := abs_sub _ _
        _ ≤ r + |a| := by linarith
    calc ‖η y • e + (inner ℝ e y - a) • gradient η y‖
        ≤ ‖η y • e‖ + ‖(inner ℝ e y - a) • gradient η y‖ := norm_add_le _ _
      _ = |η y| * ‖e‖ + |inner ℝ e y - a| * ‖gradient η y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * 1 + (r + |a|) * L := by
          apply add_le_add
          · exact mul_le_mul (hη1 y) he (norm_nonneg _) zero_le_one
          · exact mul_le_mul hin (hηL y) (norm_nonneg _) (by positivity)
      _ = 1 + (r + |a|) * L := by ring
  · have h0 : η y = 0 := image_eq_zero_of_notMem_tsupport hy
    have h1 : gradient η y = 0 := by simp [gradient, fderiv_of_notMem_tsupport ℝ hy]
    rw [h0, h1, zero_smul, smul_zero, add_zero, norm_zero]
    positivity

/-! ### HA5 under the sharp energy bound -/

/-- The vertical height weight `w(y) = (y_last - a) η(y)`, the case `e = verticalDirection m` of
`heightWeight_props` in the vertical coordinates of `SerrinEpigraph.DiffuseGoodLayers`. -/
theorem heightWeight_last_props {k : ℕ} (a : ℝ) {η : Space (k + 1) → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) {r L : ℝ} (hr : 0 ≤ r)
    (hηs : tsupport η ⊆ closedBall 0 r) (hη1 : ∀ y, |η y| ≤ 1)
    (hηL : ∀ y, ‖gradient η y‖ ≤ L) :
    ContDiff ℝ 1 (fun y : Space (k + 1) ↦ (y (Fin.last k) - a) * η y) ∧
      HasCompactSupport (fun y : Space (k + 1) ↦ (y (Fin.last k) - a) * η y) ∧
      tsupport (fun y : Space (k + 1) ↦ (y (Fin.last k) - a) * η y) ⊆ tsupport η ∧
      ∀ y, ‖gradient (fun y : Space (k + 1) ↦ (y (Fin.last k) - a) * η y) y‖ ≤
        1 + (r + |a|) * L := by
  have hfun : (fun y : Space (k + 1) ↦ (y (Fin.last k) - a) * η y) =
      fun y ↦ (inner ℝ (verticalDirection k) y - a) * η y := by
    funext y
    rw [real_inner_comm, inner_verticalDirection_right]
  rw [hfun]
  exact heightWeight_props (norm_verticalDirection k).le a hη hηc hr hηs hη1 hηL

/-- Rotations preserve the diffuse gradient mass of origin-centered balls. -/
private theorem setIntegral_ball_gradSq_comp_isometry {d : ℕ} (w : Space d → ℝ)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (R r : ℝ) :
    (∫ y in ball (0 : Space d) r, ‖gradient (fun z ↦ w (Q z)) y‖ ^ 2 / R) =
      ∫ y in ball (0 : Space d) r, ‖gradient w y‖ ^ 2 / R := by
  have hpt : ∀ y, ‖gradient (fun z ↦ w (Q z)) y‖ ^ 2 / R = ‖gradient w (Q y)‖ ^ 2 / R := by
    intro y
    rw [gradient_comp_linearIsometryEquiv, LinearIsometryEquiv.norm_map]
  simp_rw [hpt]
  have hh := (Q.measurePreserving.restrict_preimage (s := ball 0 r)
    measurableSet_ball).integral_comp Q.toHomeomorph.measurableEmbedding
    (fun z ↦ ‖gradient w z‖ ^ 2 / R)
  simpa only [Q.preimage_ball, map_zero] using hh


/-- **HA5.b and HA5.c under the sharp all-center energy bound.** There are `b` and `C`,
independent of the center `x`, the scale `R`, the band number `N`, the radius `r`, the weight `w`
and its gradient bound `G`, such that for `0 < β`, `2β ≤ b`, `N ≥ 1` and every compactly
supported `C¹` weight `w` supported in `ball 0 r` with `|∇w| ≤ G`, the rescaled translate
`v y = U(x + R • Q y)` and `ρ = |∇v|² / R` satisfy
* (total bound) `∫ ρ w² ≤ C (G/R)² r^m + C ∫_{v < 1 - β} ρ w²`;
* (small tails) `∫_{v ≥ 1 - β / 2^N} ρ w² ≤ C (G/R)² r^m + (C/N) ∫_{v < 1 - β} ρ w²`.
With `w = (t - a) η` and `ε = 1/R`, the first term is `O(ε²)` and the integrals over
`{v < 1 - β}` are the fixed-transition height moments of HA5.1. -/
theorem RigidityHypotheses.exists_stable_well_height_bounds_of_sharp_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    ∃ b C : ℝ, 0 < b ∧ b < 1 ∧ 0 < C ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ β : ℝ, 0 < β → 2 * β ≤ b → ∀ N : ℕ, 0 < N →
        ∀ r : ℝ, 0 < r → ∀ w : Space (m + 1) → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
          tsupport w ⊆ ball 0 r → ∀ G : ℝ, (∀ y, ‖gradient w y‖ ≤ G) →
            (∫ y, ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * w y ^ 2) ≤
                C * (G / R) ^ 2 * r ^ m +
                  C * ∫ y in {y | zeroExtension g u (x + R • Q y) < 1 - β},
                    ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * w y ^ 2 ∧
              (∫ y in {y | 1 - β / 2 ^ N ≤ zeroExtension g u (x + R • Q y)},
                ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * w y ^ 2) ≤
                C * (G / R) ^ 2 * r ^ m +
                  C / N * ∫ y in {y | zeroExtension g u (x + R • Q y) < 1 - β},
                    ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R * w y ^ 2 := by
  obtain ⟨b₁, C₁, hb₁, hb₁1, hC₁, htot⟩ := hr.exists_stable_well_total_bound h
  obtain ⟨b₂, C₂, hb₂, hb₂1, hC₂, htail⟩ := hr.exists_stable_well_tail_selection h
  set Ls := phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) with hLs
  refine ⟨min b₁ b₂, (C₁ + C₂ + C₂ * C₁) * (1 + 2 * |Ls|), lt_min hb₁ hb₂,
    (min_le_left _ _).trans_lt hb₁1, by positivity, ?_⟩
  intro x R hR Q β hβ hβb N hN r hr0 w hw hwc hwr G hG
  have hβ1 : 2 * β ≤ b₁ := hβb.trans (min_le_left _ _)
  have hβ2 : β ≤ b₂ := by linarith [min_le_right b₁ b₂]
  have htot' := htot x R hR Q β hβ hβ1 w hw hwc G hG
  have htail' := htail x R hR Q β hβ hβ2 N hN w hw hwc G hG
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • Q z) with hvdef
  have hvL : LocallyLipschitz v := h.locallyLipschitz_rescaled_translate x R Q
  have IF : Integrable (fun y ↦ ‖gradient v y‖ ^ 2 / R * w y ^ 2) :=
    integrable_gradSq_div_mul_sq hvL R hw.continuous hwc
  set I := ∫ y, ‖gradient v y‖ ^ 2 / R * w y ^ 2 with hI
  set L := ∫ y in {y | v y < 1 - β}, ‖gradient v y‖ ^ 2 / R * w y ^ 2 with hL
  set T := ∫ y in {y | 1 - β ≤ v y}, ‖gradient v y‖ ^ 2 / R * w y ^ 2 with hT
  set E := ∫ y in tsupport w, ‖gradient v y‖ ^ 2 / R with hE
  have hL0 : 0 ≤ L := integral_nonneg (fun y ↦ by positivity)
  have hE0 : 0 ≤ E := integral_nonneg (fun y ↦ by positivity)
  have hTI : T ≤ I := setIntegral_le_integral IF
    (Eventually.of_forall (fun y ↦ by simp only [Pi.zero_apply]; positivity))
  -- the sharp energy bound controls `E`
  have hEball : E ≤ ∫ y in ball (0 : Space (m + 1)) r, ‖gradient v y‖ ^ 2 / R := by
    have hint : IntegrableOn (fun y ↦ ‖gradient v y‖ ^ 2 / R) (ball (0 : Space (m + 1)) r) :=
      IntegrableOn.mono_set ((integrableOn_gradient_sq_of_locallyLipschitz hvL
        (isCompact_closedBall 0 r)).div_const R) ball_subset_closedBall
    exact setIntegral_mono_set hint
      (Eventually.of_forall (fun y ↦ by simp only [Pi.zero_apply]; positivity)) hwr.eventuallyLE
  have hkin := hr.translated_kinetic_ball_le_surface_bound h (L := Ls) hsharp x hR 0 hr0
  have hrot : (∫ y in ball (0 : Space (m + 1)) r, ‖gradient v y‖ ^ 2 / R) =
      ∫ y in ball (0 : Space (m + 1)) r,
        ‖gradient (fun z ↦ zeroExtension g u (x + R • z)) y‖ ^ 2 / R :=
    setIntegral_ball_gradSq_comp_isometry (fun z ↦ zeroExtension g u (x + R • z)) Q R r
  have hP : 0 ≤ r ^ m := by positivity
  have hE2 : E ≤ 2 * |Ls| * r ^ m := by
    have h1 : 2 * Ls * r ^ m ≤ 2 * |Ls| * r ^ m :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self Ls]) hP
    linarith
  set X := (G / R) ^ 2 with hX
  have hX0 : 0 ≤ X := sq_nonneg _
  have hXP : 0 ≤ X * r ^ m := mul_nonneg hX0 hP
  have hXE : X * E ≤ 2 * |Ls| * (X * r ^ m) := by
    calc X * E ≤ X * (2 * |Ls| * r ^ m) := mul_le_mul_of_nonneg_left hE2 hX0
      _ = 2 * |Ls| * (X * r ^ m) := by ring
  have hLs0 : 0 ≤ |Ls| := abs_nonneg _
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  set C := (C₁ + C₂ + C₂ * C₁) * (1 + 2 * |Ls|) with hCdef
  have hCC₁ : C₁ ≤ C := by
    have : C₁ ≤ C₁ + C₂ + C₂ * C₁ := by nlinarith
    calc C₁ = C₁ * 1 := (mul_one _).symm
      _ ≤ (C₁ + C₂ + C₂ * C₁) * (1 + 2 * |Ls|) :=
        mul_le_mul this (by linarith) zero_le_one (by positivity)
  have hCC₁L : C₁ * (2 * |Ls|) ≤ C := by
    have : C₁ ≤ C₁ + C₂ + C₂ * C₁ := by nlinarith
    calc C₁ * (2 * |Ls|) ≤ (C₁ + C₂ + C₂ * C₁) * (1 + 2 * |Ls|) :=
        mul_le_mul this (by linarith) (by positivity) (by positivity)
      _ = C := rfl
  have hCC₂L : (C₂ + C₂ * C₁) * (2 * |Ls|) ≤ C := by
    have : C₂ + C₂ * C₁ ≤ C₁ + C₂ + C₂ * C₁ := by linarith
    calc (C₂ + C₂ * C₁) * (2 * |Ls|) ≤ (C₁ + C₂ + C₂ * C₁) * (1 + 2 * |Ls|) :=
        mul_le_mul this (by linarith) (by positivity) (by positivity)
      _ = C := rfl
  have hCC₂₁ : C₂ * C₁ ≤ C := by
    have : C₂ * C₁ ≤ C₁ + C₂ + C₂ * C₁ := by linarith
    calc C₂ * C₁ = C₂ * C₁ * 1 := (mul_one _).symm
      _ ≤ (C₁ + C₂ + C₂ * C₁) * (1 + 2 * |Ls|) :=
        mul_le_mul this (by linarith) zero_le_one (by positivity)
  -- total bound
  have hItot : I ≤ C₁ * (2 * |Ls|) * (X * r ^ m) + C₁ * L := by
    have h1 := mul_le_mul_of_nonneg_left hXE hC₁.le
    calc I ≤ C₁ * X * E + C₁ * L := htot'
      _ = C₁ * (X * E) + C₁ * L := by ring
      _ ≤ C₁ * (2 * |Ls| * (X * r ^ m)) + C₁ * L := by linarith
      _ = C₁ * (2 * |Ls|) * (X * r ^ m) + C₁ * L := by ring
  refine ⟨?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_right hCC₁L hXP
    have h2 := mul_le_mul_of_nonneg_right hCC₁ hL0
    calc I ≤ C₁ * (2 * |Ls|) * (X * r ^ m) + C₁ * L := hItot
      _ ≤ C * (X * r ^ m) + C * L := by linarith
      _ = C * X * r ^ m + C * L := by ring
  · -- tails
    have hT' : T ≤ C₁ * (2 * |Ls|) * (X * r ^ m) + C₁ * L := hTI.trans hItot
    have hdivN : C₂ / N ≤ C₂ := div_le_self hC₂.le hN1
    have hdiv0 : 0 ≤ C₂ / N := by positivity
    have h1 : C₂ / N * T ≤ C₂ / N * (C₁ * (2 * |Ls|) * (X * r ^ m) + C₁ * L) :=
      mul_le_mul_of_nonneg_left hT' hdiv0
    have h2 : C₂ / N * (C₁ * (2 * |Ls|) * (X * r ^ m)) ≤ C₂ * (C₁ * (2 * |Ls|) * (X * r ^ m)) :=
      mul_le_mul_of_nonneg_right hdivN (by positivity)
    have h3 : C₂ * X * E ≤ C₂ * (2 * |Ls|) * (X * r ^ m) := by
      have := mul_le_mul_of_nonneg_left hXE hC₂.le
      calc C₂ * X * E = C₂ * (X * E) := by ring
        _ ≤ C₂ * (2 * |Ls| * (X * r ^ m)) := this
        _ = C₂ * (2 * |Ls|) * (X * r ^ m) := by ring
    have h4 : (C₂ + C₂ * C₁) * (2 * |Ls|) * (X * r ^ m) ≤ C * (X * r ^ m) :=
      mul_le_mul_of_nonneg_right hCC₂L hXP
    have h5 : C₂ / N * (C₁ * L) = (C₂ * C₁) / N * L := by ring
    have h6 : (C₂ * C₁) / N * L ≤ C / N * L :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCC₂₁ hNpos.le) hL0
    calc (∫ y in {y | 1 - β / 2 ^ N ≤ v y}, ‖gradient v y‖ ^ 2 / R * w y ^ 2)
        ≤ C₂ * X * E + C₂ / N * T := htail'
      _ ≤ C * (X * r ^ m) + C / N * L := by
          have e1 : C₂ / N * (C₁ * (2 * |Ls|) * (X * r ^ m) + C₁ * L) =
              C₂ / N * (C₁ * (2 * |Ls|) * (X * r ^ m)) + C₂ / N * (C₁ * L) := by ring
          have e2 : C₂ * (2 * |Ls|) * (X * r ^ m) + C₂ * (C₁ * (2 * |Ls|) * (X * r ^ m)) =
              (C₂ + C₂ * C₁) * (2 * |Ls|) * (X * r ^ m) := by ring
          linarith
      _ = C * X * r ^ m + C / N * L := by ring

end SerrinEpigraph
