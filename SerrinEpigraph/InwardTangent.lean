module

public import SerrinEpigraph.BoundaryGradient
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Inward directions in the positive tangent cone
-/

public section

open Set Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

/-- The right-hand velocity of a differentiable curve remaining in a set is an inward
tangent direction to that set. -/
theorem curve_derivative_mem_posTangentConeAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} {w : E} {S : Set E} (hd : HasDerivAt γ w 0)
    (hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ S) :
    w ∈ posTangentConeAt S (γ 0) := by
  apply mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ))
    (fun t ↦ (Real.toNNReal t)⁻¹) (fun t ↦ γ t - γ 0)
  · simpa only [sub_self] using
      (hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub
        (tendsto_const_nhds (x := γ 0))
  · simpa only [add_sub_cancel] using hmem
  · have hh := hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [slope_def_module, sub_zero, NNReal.smul_def, NNReal.coe_inv,
      Real.coe_toNNReal _ ht.le]

/-- Every direction above the tangent hyperplane is realized by a curve in the closed epigraph. -/
theorem point_mem_posTangentConeAt_epigraph {m : ℕ} {g : Space m → ℝ} {y a : Space m}
    (hg : DifferentiableAt ℝ g y) {b : ℝ} (hb : fderiv ℝ g y a ≤ b) :
    point a b ∈ posTangentConeAt (closure (epigraph g)) (point y (g y)) := by
  let q : ℝ → Space m := fun t ↦ y + t • a
  let γ : ℝ → Space (m + 1) := fun t ↦
    point (q t) (g (q t) + t * (b - fderiv ℝ g y a))
  have hq : HasDerivAt q a 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add y using 1
    · rfl
    · simp
  have hq0 : q 0 = y := by simp [q]
  have hgq : HasDerivAt (fun t ↦ g (q t)) (fderiv ℝ g y a) 0 := by
    have hh : HasFDerivAt g (fderiv ℝ g y) (q 0) := hq0 ▸ hg.hasFDerivAt
    exact hh.comp_hasDerivAt 0 hq
  have ht := (hasDerivAt_id (0 : ℝ)).mul_const (b - fderiv ℝ g y a)
  have hv : HasDerivAt (fun t ↦ g (q t) + t * (b - fderiv ℝ g y a)) b 0 := by
    convert hgq.add ht using 1
    · rfl
    · simp
  have hγ : HasDerivAt γ (point a b) 0 := by
    exact pointContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (hq.prodMk hv)
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ closure (epigraph g) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply point_mem_closure_epigraph
    exact le_add_of_nonneg_right (mul_nonneg (show 0 ≤ t from le_of_lt ht) (sub_nonneg.mpr hb))
  have hh := curve_derivative_mem_posTangentConeAt hγ hmem
  simpa only [γ, hq0, zero_mul, add_zero] using hh

/-- The inward unit normal belongs to the closed epigraph's positive tangent cone. -/
theorem neg_outwardNormal_mem_posTangentConeAt {m : ℕ} {g : Space m → ℝ} {y : Space m}
    (hg : DifferentiableAt ℝ g y) :
    -outwardNormal g y ∈ posTangentConeAt (closure (epigraph g)) (point y (g y)) := by
  let r := (Real.sqrt (1 + ‖gradient g y‖ ^ 2))⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hder : fderiv ℝ g y (-(r • gradient g y)) = -r * ‖gradient g y‖ ^ 2 := by
    rw [map_neg, map_smul, smul_eq_mul, ← inner_gradient_left,
      real_inner_self_eq_norm_sq]
    ring
  have hh := point_mem_posTangentConeAt_epigraph hg (a := -(r • gradient g y))
    (b := r) (by rw [hder]; nlinarith [sq_nonneg ‖gradient g y‖])
  convert hh using 1
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [outwardNormal, point, r]

end SerrinEpigraph
