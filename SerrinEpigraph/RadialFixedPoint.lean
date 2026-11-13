module

public import SerrinEpigraph.RadialIntegral
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Fixed points for the radial integral equation
-/

public section
noncomputable section
open Set
open scoped NNReal

namespace SerrinEpigraph

/-- Extend a continuous radius profile constantly beyond its interval endpoints. -/
@[expose] def radialExtend {R : ℝ} (hR : 0 ≤ R) (q : C(Icc (0 : ℝ) R, ℝ)) : ℝ → ℝ :=
  fun r ↦ q (projIcc 0 R hR r)

/-- The constant endpoint extension is continuous. -/
theorem radialExtend_continuous {R : ℝ} (hR : 0 ≤ R) (q : C(Icc (0 : ℝ) R, ℝ)) :
    Continuous (radialExtend hR q) :=
  q.continuous.comp continuous_projIcc

/-- Restrict the radial integral operator to a compact interval. -/
@[expose] def radialPicardMap (m : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    C(Icc (0 : ℝ) R, ℝ) → C(Icc (0 : ℝ) R, ℝ) := fun q ↦
  ⟨fun r ↦ radialPicard m f a (radialExtend hR q) r,
    (continuous_iff_continuousAt.mpr (fun r ↦
      (radialPicard_hasDerivAt m a r (hf.comp (radialExtend_continuous hR q))).continuousAt)).comp
      continuous_subtype_val⟩

/-- The radial Picard operator has the expected quadratic Lipschitz bound. -/
theorem radialPicardMap_dist_le (m : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (a : ℝ)
    (q w : C(Icc (0 : ℝ) R, ℝ)) :
    dist (radialPicardMap m hR hf.continuous a q) (radialPicardMap m hR hf.continuous a w) ≤
      (R ^ 2 / 2 * ((L : ℝ) / (m + 1 : ℝ))) * dist q w := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro r
  change dist (radialPicard m f a (radialExtend hR q) r)
    (radialPicard m f a (radialExtend hR w) r) ≤ _
  rw [dist_eq_norm]
  have he := radialPicard_norm_sub_picard_le m
    (hf.continuous.comp (radialExtend_continuous hR q))
    (hf.continuous.comp (radialExtend_continuous hR w)) r.property.1
    (M := (L : ℝ) * dist q w) (a := a) (by
      intro t ht
      rw [← dist_eq_norm]
      exact (hf.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
        (ContinuousMap.dist_apply_le_dist (f := q) (g := w) (projIcc 0 R hR t)) L.coe_nonneg))
  refine he.trans ?_
  have hr2 : (r : ℝ) ^ 2 ≤ R ^ 2 := by nlinarith [r.property.1, r.property.2]
  calc
    _ ≤ R ^ 2 / 2 * (((L : ℝ) * dist q w) / (m + 1 : ℝ)) := by
      gcongr
    _ = _ := by ring

/-- For sufficiently short intervals the radial integral equation has a continuous solution. -/
theorem exists_radial_integral_solution (m : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (a : ℝ)
    (hsmall : R ^ 2 / 2 * ((L : ℝ) / (m + 1 : ℝ)) < 1) :
    ∃ q : C(Icc (0 : ℝ) R, ℝ),
      ∀ r : Icc (0 : ℝ) R, q r = radialPicard m f a (radialExtend hR q) r := by
  let K : ℝ≥0 := ⟨R ^ 2 / 2 * ((L : ℝ) / (m + 1 : ℝ)), by positivity⟩
  have hc : ContractingWith K (radialPicardMap m hR hf.continuous a) := by
    refine ⟨hsmall, LipschitzWith.of_dist_le_mul ?_⟩
    intro q w
    exact radialPicardMap_dist_le m hR hf a q w
  refine ⟨hc.fixedPoint _, fun r ↦ ?_⟩
  have he := congrArg (fun q : C(Icc (0 : ℝ) R, ℝ) ↦ q r) hc.fixedPoint_isFixedPt
  exact he.symm

/-- On a short interval the integral solution is unique. -/
theorem radial_integral_solution_unique (m : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (a : ℝ)
    (hsmall : R ^ 2 / 2 * ((L : ℝ) / (m + 1 : ℝ)) < 1)
    {q w : C(Icc (0 : ℝ) R, ℝ)}
    (hq : ∀ r, q r = radialPicard m f a (radialExtend hR q) r)
    (hw : ∀ r, w r = radialPicard m f a (radialExtend hR w) r) : q = w := by
  have hq' : radialPicardMap m hR hf.continuous a q = q := by
    ext r
    exact (hq r).symm
  have hw' : radialPicardMap m hR hf.continuous a w = w := by
    ext r
    exact (hw r).symm
  have he := radialPicardMap_dist_le m hR hf a q w
  rw [hq', hw'] at he
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := q) (y := w)]

/-- The fixed point gives a differentiable profile satisfying the averaged radial equation. -/
theorem exists_radial_averaged_solution (m : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (a : ℝ)
    (hsmall : R ^ 2 / 2 * ((L : ℝ) / (m + 1 : ℝ)) < 1) :
    ∃ Q : ℝ → ℝ, Continuous Q ∧ Q 0 = a ∧ HasDerivAt Q 0 0 ∧
      ∀ r ∈ Icc (0 : ℝ) R,
        HasDerivAt Q (-r * radialAverage m (f ∘ Q) r) r := by
  obtain ⟨q, hq⟩ := exists_radial_integral_solution m hR hf a hsmall
  let Q := radialPicard m f a (radialExtend hR q)
  have hcont : Continuous (f ∘ radialExtend hR q) :=
    hf.continuous.comp (radialExtend_continuous hR q)
  have heq : EqOn Q (radialExtend hR q) (Icc 0 R) := by
    intro t ht
    change radialPicard m f a (radialExtend hR q) t = q (projIcc 0 R hR t)
    rw [projIcc_of_mem hR ht]
    exact (hq ⟨t, ht⟩).symm
  refine ⟨Q, continuous_iff_continuousAt.mpr (fun r ↦
    (radialPicard_hasDerivAt m a r hcont).continuousAt),
    radialPicard_zero m f a _, radialPicard_hasDerivAt_zero m a hcont, ?_⟩
  intro r hr
  have havg : radialAverage m (f ∘ Q) r =
      radialAverage m (f ∘ radialExtend hR q) r := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
    have ht : r * s ∈ Icc (0 : ℝ) R :=
      ⟨mul_nonneg hr.1 hs'.1, (mul_le_of_le_one_right hr.1 hs'.2).trans hr.2⟩
    simp only [Function.comp_apply, heq ht]
  rw [havg]
  exact radialPicard_hasDerivAt m a r hcont

end SerrinEpigraph
