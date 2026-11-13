module

public import SerrinEpigraph.DilationStationarity
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating radial energy cutoffs with respect to scale
-/

public section

noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- A scalar profile evaluated at squared distance divided by squared scale. -/
@[expose] def radialWeight {d : ℕ} (q : ℝ → ℝ) (c : Space d) (R : ℝ)
    (x : Space d) : ℝ := q (‖x - c‖ ^ 2 / R ^ 2)

/-- The derivative of a radial weight with respect to its positive scale. -/
@[expose] def radialWeightScaleDerivative {d : ℕ} (q : ℝ → ℝ) (c : Space d)
    (R : ℝ) (x : Space d) : ℝ :=
  -2 * ‖x - c‖ ^ 2 / R ^ 3 * deriv q (‖x - c‖ ^ 2 / R ^ 2)

/-- C1 profiles give C1 spatial weights, including at the center. -/
theorem contDiff_radialWeight {d : ℕ} {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    (c : Space d) (R : ℝ) : ContDiff ℝ 1 (radialWeight q c R) :=
  hq.comp (((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)).div_const (R ^ 2))

/-- Spatial differentiation of a radial energy weight. -/
theorem fderiv_radialWeight {d : ℕ} {q : ℝ → ℝ} (hq : Differentiable ℝ q)
    (c : Space d) (R : ℝ) (x v : Space d) :
    fderiv ℝ (radialWeight q c R) x v =
      2 / R ^ 2 * deriv q (‖x - c‖ ^ 2 / R ^ 2) * inner ℝ (x - c) v := by
  have hdist := ((hasFDerivAt_id x).sub_const c).norm_sq
  have hscale := hdist.smul_const ((R ^ 2)⁻¹)
  have hcomp := (hq (‖x - c‖ ^ 2 / R ^ 2)).hasDerivAt.comp_hasFDerivAt x
    (show HasFDerivAt (fun y ↦ ‖y - c‖ ^ 2 / R ^ 2) _ x from by
      simpa only [smul_eq_mul, ← div_eq_mul_inv, id_eq] using hscale)
  change HasFDerivAt (radialWeight q c R) _ x at hcomp
  rw [hcomp.fderiv]
  simp [div_eq_mul_inv, inner_sub_left]
  ring

/-- Scale differentiation only needs the profile's first derivative. -/
theorem hasDerivAt_radialWeight_scale {d : ℕ} {q : ℝ → ℝ} (hq : Differentiable ℝ q)
    (c : Space d) {R : ℝ} (hR : 0 < R) (x : Space d) :
    HasDerivAt (fun r ↦ radialWeight q c r x) (radialWeightScaleDerivative q c R x) R := by
  have hs := (hasDerivAt_const R (‖x - c‖ ^ 2)).div ((hasDerivAt_id R).pow 2)
    (pow_ne_zero 2 hR.ne')
  have hd := (hq (‖x - c‖ ^ 2 / R ^ 2)).hasDerivAt.comp R hs
  convert hd using 1
  · rfl
  · dsimp [radialWeightScaleDerivative]
    field_simp
    ring

/-- A profile vanishing beyond two yields a compactly supported spatial weight. -/
theorem tsupport_radialWeight_subset {d : ℕ} {q : ℝ → ℝ}
    (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0) (c : Space d) {R : ℝ} (hR : 0 < R) :
    tsupport (radialWeight q c R) ⊆ closedBall c (2 * R) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  have hdist : 2 * R < ‖x - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hn
  have hratio : 2 ≤ ‖x - c‖ ^ 2 / R ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [norm_nonneg (x - c)]
  exact hx (hzero _ hratio)

/-- A profile which vanishes on an upper half-line has zero derivative in its interior. -/
theorem deriv_eq_zero_of_zero_above {q : ℝ → ℝ}
    (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0) {t : ℝ} (ht : 2 < t) : deriv q t = 0 := by
  apply HasDerivAt.deriv
  apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact hzero s hs.le

/-- The scale derivative has the same uniform spatial support bound as the weight. -/
theorem tsupport_radialWeightScaleDerivative_subset {d : ℕ} {q : ℝ → ℝ}
    (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0) (c : Space d) {R : ℝ} (hR : 0 < R) :
    tsupport (radialWeightScaleDerivative q c R) ⊆ closedBall c (2 * R) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  have hdist : 2 * R < ‖x - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hn
  have hratio : 2 < ‖x - c‖ ^ 2 / R ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [norm_nonneg (x - c)]
  exact hx (by simp [radialWeightScaleDerivative, deriv_eq_zero_of_zero_above hzero hratio])

/-- Scale derivatives are jointly continuous away from scale zero. -/
theorem continuousOn_radialWeightScaleDerivative {d : ℕ} {q : ℝ → ℝ}
    (hq : ContDiff ℝ 1 q) (c : Space d) :
    ContinuousOn (fun p : ℝ × Space d ↦ radialWeightScaleDerivative q c p.1 p.2)
      (Ioi 0 ×ˢ univ) := by
  have hn : Continuous (fun p : ℝ × Space d ↦ ‖p.2 - c‖ ^ 2) := by fun_prop
  have hder := hq.continuous_deriv le_rfl
  have hquot : ContinuousOn (fun p : ℝ × Space d ↦ ‖p.2 - c‖ ^ 2 / p.1 ^ 2)
      (Ioi 0 ×ˢ univ) := hn.continuousOn.div (continuous_fst.pow 2).continuousOn
        (fun p hp ↦ pow_ne_zero 2 (ne_of_gt hp.1))
  exact ((continuous_const.mul hn).continuousOn.div (continuous_fst.pow 3).continuousOn
    (fun p hp ↦ pow_ne_zero 3 (ne_of_gt hp.1))).mul (hder.comp_continuousOn hquot)

/-- On a fixed compact set the scale derivative passes under an integral with
any integrable energy density. The density itself need not be continuous. -/
theorem hasDerivAt_integral_mul_radialWeight_on_compact {d : ℕ} {q : ℝ → ℝ}
    (hq : ContDiff ℝ 1 q) (c : Space d) {R : ℝ} (hR : 0 < R)
    {K : Set (Space d)} (hK : IsCompact K) {w : Space d → ℝ} (hw : IntegrableOn w K) :
    HasDerivAt (fun r ↦ ∫ x in K, w x * radialWeight q c r x)
      (∫ x in K, w x * radialWeightScaleDerivative q c R x) R := by
  let J := Icc (R / 2) (2 * R)
  have hJ : J ⊆ Ioi (0 : ℝ) := by
    intro r hr
    change 0 < r
    linarith [hr.1]
  have hcont : ContinuousOn
      (fun p : ℝ × Space d ↦ radialWeightScaleDerivative q c p.1 p.2) (J ×ˢ K) :=
    (continuousOn_radialWeightScaleDerivative hq c).mono (prod_mono hJ (subset_univ K))
  have hJK : IsCompact (J ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C, hC⟩ := hJK.exists_bound_of_continuousOn hcont
  have hF (r : ℝ) : Continuous (radialWeight q c r) := (contDiff_radialWeight hq c r).continuous
  have hF' (r : ℝ) (hr : 0 < r) : Continuous (radialWeightScaleDerivative q c r) := by
    have hp : Continuous (fun x : Space d ↦ (r, x)) := continuous_const.prodMk continuous_id
    have ht := (continuousOn_radialWeightScaleDerivative hq c).comp hp.continuousOn
      (show MapsTo (fun x : Space d ↦ (r, x)) univ (Ioi 0 ×ˢ univ) from
        fun x _ ↦ ⟨hr, mem_univ x⟩)
    exact continuousOn_univ.mp ht
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict K)
    (s := Ioo (R / 2) (2 * R)) (bound := fun x ↦ ‖w x‖ * C)
    (F := fun r x ↦ w x * radialWeight q c r x)
    (F' := fun r x ↦ w x * radialWeightScaleDerivative q c r x)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun r ↦ hw.aestronglyMeasurable.mul (hF r).aestronglyMeasurable))
    (hw.mul_continuousOn (hF R).continuousOn hK)
    (hw.aestronglyMeasurable.mul (hF' R hR).aestronglyMeasurable) ?_
    (hw.norm.mul_const C) ?_).2
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    intro r hr
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC (r, x) ⟨⟨hr.1.le, hr.2.le⟩, hx⟩) (norm_nonneg _)
  · exact Eventually.of_forall (fun x r hr ↦
      (hasDerivAt_radialWeight_scale hq.differentiable_one c (hJ ⟨hr.1.le, hr.2.le⟩) x).const_mul
        (w x))

/-- Compact radial support allows differentiation of the full-space weighted energy,
requiring only local integrability of the density. -/
theorem hasDerivAt_integral_mul_radialWeight {d : ℕ} {q : ℝ → ℝ}
    (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (c : Space d) {R : ℝ} (hR : 0 < R) {w : Space d → ℝ}
    (hw : ∀ K : Set (Space d), IsCompact K → IntegrableOn w K) :
    HasDerivAt (fun r ↦ ∫ x, w x * radialWeight q c r x)
      (∫ x, w x * radialWeightScaleDerivative q c R x) R := by
  let K := closedBall c (4 * R)
  have hK : IsCompact K := isCompact_closedBall c (4 * R)
  have he (r : ℝ) (hr : r ∈ Ioo (R / 2) (2 * R)) :
      (∫ x in K, w x * radialWeight q c r x) = ∫ x, w x * radialWeight q c r x := by
    have hr0 : 0 < r := by linarith [hr.1]
    have hs : tsupport (radialWeight q c r) ⊆ K :=
      (tsupport_radialWeight_subset hzero c hr0).trans (closedBall_subset_closedBall (by
        linarith [hr.2]))
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh)), mul_zero]
  have he' : (∫ x in K, w x * radialWeightScaleDerivative q c R x) =
      ∫ x, w x * radialWeightScaleDerivative q c R x := by
    have hs : tsupport (radialWeightScaleDerivative q c R) ⊆ K :=
      (tsupport_radialWeightScaleDerivative_subset hzero c hR).trans
        (closedBall_subset_closedBall (by linarith))
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh)), mul_zero]
  have hd := hasDerivAt_integral_mul_radialWeight_on_compact hq c hR hK (hw K hK)
  rw [he'] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (show R / 2 < R by linarith)
    (show R < 2 * R by linarith)] with r hr
  exact (he r hr).symm

end SerrinEpigraph
