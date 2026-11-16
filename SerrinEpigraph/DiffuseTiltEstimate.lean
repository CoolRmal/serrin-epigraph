module

public import SerrinEpigraph.PlaneTiltConvergence
public import SerrinEpigraph.ModicaBound

/-!
# Diffuse tilt controlled by the oriented primitive defect
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- The diffuse tangential Dirichlet density at dilation scale `R`. -/
@[expose] def diffuseTiltDensity {d : ℕ} (R : ℝ) (v : Space d → ℝ)
    (e x : Space d) : ℝ :=
  (‖gradient v x‖ ^ 2 - inner ℝ (gradient v x) e ^ 2) / R

/-- The squared component in a unit direction is bounded by the squared norm. -/
theorem inner_sq_le_norm_sq_of_unit {d : ℕ} (q : Space d) {e : Space d}
    (he : ‖e‖ = 1) : inner ℝ q e ^ 2 ≤ ‖q‖ ^ 2 := by
  have hh := abs_real_inner_le_norm q e
  rw [he, mul_one] at hh
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg q)).mpr hh

/-- Diffuse tilt is nonnegative for every unit direction and positive scale. -/
theorem diffuseTiltDensity_nonneg {d : ℕ} {R : ℝ} (hR : 0 < R)
    (v : Space d → ℝ) {e : Space d} (he : ‖e‖ = 1) (x : Space d) :
    0 ≤ diffuseTiltDensity R v e x :=
  div_nonneg (sub_nonneg.mpr (inner_sq_le_norm_sq_of_unit (gradient v x) he)) hR.le

/-- The tangential Dirichlet density is integrable on compact sets. -/
theorem integrableOn_diffuseTiltDensity {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {K : Set (Space d)} (hK : IsCompact K)
    (R : ℝ) {e : Space d} (he : ‖e‖ = 1) :
    IntegrableOn (diffuseTiltDensity R v e) K := by
  have hi := integrableOn_gradient_sq_of_locallyLipschitz hv hK
  have hp : IntegrableOn (fun x ↦ inner ℝ (gradient v x) e ^ 2) K := by
    apply hi.mono'
      (((measurable_gradient v).inner (𝕜 := ℝ) measurable_const).pow_const 2).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact inner_sq_le_norm_sq_of_unit (gradient v x) he
  exact (hi.sub hp).div_const R

/-- The elementary Modica comparison retains the full oriented defect, including
points where the normal points in the opposite direction. -/
theorem tangential_energy_le_oriented_weighted_defect {d : ℕ}
    (q : Space d) {e : Space d} (he : ‖e‖ = 1) {R w : ℝ}
    (hR : 0 < R) (hw : 0 ≤ w) (hq : ‖q‖ ≤ R * w) :
    (‖q‖ ^ 2 - inner ℝ q e ^ 2) / R ≤
      2 * (‖w • q‖ - inner ℝ (w • q) e) := by
  have hd := oriented_gradient_defect_nonneg q he
  have hm := mul_le_mul_of_nonneg_right hq hd
  rw [norm_smul, Real.norm_of_nonneg hw, real_inner_smul_left]
  apply (div_le_iff₀ hR).mpr
  nlinarith [sq_nonneg (‖q‖ - inner ℝ q e)]

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Modica's bound extends to the totalized gradient on the zero phase. -/
theorem RigidityHypotheses.norm_gradient_zeroExtension_le_sqrt_potential
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    ‖gradient (zeroExtension g u) x‖ ≤
      Real.sqrt (2 * normalizedPotential f (zeroExtension g u x)) := by
  by_cases hx : x ∈ epigraph g
  · rw [h.gradient_zeroExtension hx, zeroExtension_of_mem hx]
    have hh := hr.modica_bound h hx
    have hs : ‖gradient u x‖ ^ 2 ≤ 2 * normalizedPotential f (u x) := by linarith
    simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hs
  · rw [h.gradient_zeroExtension_of_notMem hx, norm_zero]
    exact Real.sqrt_nonneg _

/-- Actual rescaled diffuse tilt is bounded pointwise by twice the oriented
defect of the actual rescaled phase primitive. -/
theorem RigidityHypotheses.diffuseTiltDensity_le_primitive_defect
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℝ} (hR : 0 < R) {e : Space (m + 1)} (he : ‖e‖ = 1)
    (x : Space (m + 1)) :
    diffuseTiltDensity R (fun y ↦ zeroExtension g u (R • y)) e x ≤
      2 * (‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x‖ -
        inner ℝ (gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x) e) := by
  let w := Real.sqrt (2 * normalizedPotential f (zeroExtension g u (R • x)))
  have hq : ‖gradient (fun y ↦ zeroExtension g u (R • y)) x‖ ≤ R * w := by
    rw [gradient_comp_dilation, norm_smul, Real.norm_of_nonneg hR.le]
    exact mul_le_mul_of_nonneg_left (hr.norm_gradient_zeroExtension_le_sqrt_potential h _)
      hR.le
  have hp : gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x =
      w • gradient (fun y ↦ zeroExtension g u (R • y)) x := by
    rw [gradient_comp_dilation (fun y ↦ phasePrimitive f (zeroExtension g u y)),
      hr.gradient_phasePrimitive_zeroExtension h, gradient_comp_dilation]
    simp only [w, smul_smul, mul_comm]
  rw [hp]
  exact tangential_energy_le_oriented_weighted_defect _ he hR (Real.sqrt_nonneg _) hq

/-- The pointwise Modica comparison gives an actual local integral estimate. -/
theorem RigidityHypotheses.integral_diffuseTilt_le_primitive_defect
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℝ} (hR : 0 < R) {e : Space (m + 1)} (he : ‖e‖ = 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    (∫ x in K, diffuseTiltDensity R (fun y ↦ zeroExtension g u (R • y)) e x) ≤
      2 * ∫ x in K,
        ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x‖ -
          inner ℝ (gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x) e := by
  have hv := h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul R).locallyLipschitz
  have hp := (hr.phasePrimitive_zeroExtension_locallyLipschitz h).comp
    (lipschitzWith_smul R).locallyLipschitz
  have hg := integrableOn_gradient_of_locallyLipschitz hp hK
  have hgi : IntegrableOn (fun x ↦ inner ℝ
      (gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x) e) K :=
    hg.inner_const e
  rw [← integral_const_mul]
  exact integral_mono (integrableOn_diffuseTiltDensity hv hK R he)
    ((hg.norm.sub hgi).const_mul 2) (hr.diffuseTiltDensity_le_primitive_defect h hR he)

end SerrinEpigraph
