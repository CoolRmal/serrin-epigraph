module

public import SerrinEpigraph.SimonsConeIntegral
public import SerrinEpigraph.ConeClassificationInduction
public import SerrinEpigraph.PerimeterRadonGlobal

/-!
# Vanishing of the second fundamental form of low-dimensional regular minimizing cones

Let `T ⊆ ℝᵏ`, `3 ≤ k ≤ 7`, be a minimizing cone all of whose boundary points other than the vertex
lie in smooth boundary charts. Then the second fundamental form vanishes at every such point
(`Simons.secondFundamentalForm_eq_zero_of_cone`).

The proof is the radial argument of GR2 carried out on `M` itself instead of on the link:
1. the perimeter measure `μ` of a cone scales like `μ (s B) = s^{k-1} μ B`
   (`Simons.map_smul_perimeterMeasure`), and `|A|²` is homogeneous of degree `-2`, so the
   functional `Ψ g = ∫ |A|² |x|^{3-k} g (log |x|) dμ` is invariant under integer translations of
   `g` (`Simons.translate_eq`);
2. the stability inequality of `SerrinEpigraph.SimonsConeIntegral`, tested with the radial
   profile `φ(r) = r^{(5-k)/2} v(log r)` for a smooth plateau `v` equal to `1` on `[-L, L]`,
   reads `Ψ (2 v² - (α v + v')²) ≤ 0` with `α = (5 - k)/2`;
3. since `α² ≤ 1 < 2`, the integrand is `≥ 1` on `(-L, L)` and bounded below on the two unit
   layers at the ends, so `(2L - 2) q ≤ 4 C q` for `q = Ψ 1_{[0,1)} ≥ 0`, whence `q = 0` for `L`
   large; continuity and the positivity of `μ` on `M` then give `|A|² = 0`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff ENNReal

namespace SerrinEpigraph

namespace Simons

/-! ### 1. A smooth plateau and the radial profile -/

section Profile

/-- The smooth plateau `v_L`: equal to `1` on `[-L, L]` and to `0` outside `(-L-1, L+1)`. -/
def plateau (L t : ℝ) : ℝ :=
  Real.smoothTransition (t + (L + 1)) * Real.smoothTransition ((L + 1) - t)

theorem contDiff_plateau (L : ℝ) : ContDiff ℝ ∞ (plateau L) :=
  ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.add contDiff_const)).mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_id))

theorem plateau_nonneg (L t : ℝ) : 0 ≤ plateau L t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem plateau_le_one (L t : ℝ) : plateau L t ≤ 1 := by
  have h1 := Real.smoothTransition.le_one (t + (L + 1))
  have h2 := Real.smoothTransition.le_one ((L + 1) - t)
  have h3 := Real.smoothTransition.nonneg (t + (L + 1))
  have h4 := Real.smoothTransition.nonneg ((L + 1) - t)
  unfold plateau
  nlinarith

theorem plateau_eq_zero {L t : ℝ} (ht : t ≤ -(L + 1) ∨ L + 1 ≤ t) : plateau L t = 0 := by
  unfold plateau
  rcases ht with ht | ht
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (show (L + 1) - t ≤ 0 by linarith), mul_zero]

theorem plateau_eventually_one {L t : ℝ} (ht : t ∈ Ioo (-L) L) :
    plateau L =ᶠ[𝓝 t] fun _ ↦ 1 := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  unfold plateau
  rw [Real.smoothTransition.one_of_one_le (by linarith [hs.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hs.2]), one_mul]

theorem plateau_eventually_zero {L t : ℝ} (ht : t < -(L + 1) ∨ L + 1 < t) :
    plateau L =ᶠ[𝓝 t] fun _ ↦ 0 := by
  rcases ht with ht | ht
  · filter_upwards [Iio_mem_nhds ht] with s hs
    exact plateau_eq_zero (Or.inl hs.le)
  · filter_upwards [Ioi_mem_nhds ht] with s hs
    exact plateau_eq_zero (Or.inr hs.le)

theorem exists_bound_deriv_smoothTransition :
    ∃ C, 0 ≤ C ∧ ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ↦ ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have := hC t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have hloc : ∃ c : ℝ, Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ c := by
      rcases not_and_or.mp ht with h0 | h1
      · refine ⟨0, ?_⟩
        filter_upwards [Iio_mem_nhds (not_le.mp h0)] with s hs
        exact Real.smoothTransition.zero_of_nonpos hs.le
      · refine ⟨1, ?_⟩
        filter_upwards [Ioi_mem_nhds (not_le.mp h1)] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
    obtain ⟨c, hc'⟩ := hloc
    rw [hc'.deriv_eq, deriv_const, abs_zero]
    exact le_max_right _ _

theorem exists_bound_deriv_plateau : ∃ C, 0 ≤ C ∧ ∀ L t, |deriv (plateau L) t| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_smoothTransition
  refine ⟨2 * C, by positivity, fun L t ↦ ?_⟩
  have hσ : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
  have hd1 : DifferentiableAt ℝ (fun s ↦ Real.smoothTransition (s + (L + 1))) t :=
    (hσ _).comp t (differentiableAt_id.add_const _)
  have hd2 : DifferentiableAt ℝ (fun s ↦ Real.smoothTransition ((L + 1) - s)) t :=
    (hσ _).comp t (differentiableAt_id.const_sub _)
  have hderiv : deriv (plateau L) t =
      deriv Real.smoothTransition (t + (L + 1)) * Real.smoothTransition ((L + 1) - t) +
        Real.smoothTransition (t + (L + 1)) * -deriv Real.smoothTransition ((L + 1) - t) := by
    rw [show plateau L = fun s ↦ Real.smoothTransition (s + (L + 1)) *
      Real.smoothTransition ((L + 1) - s) from rfl, deriv_fun_mul hd1 hd2, deriv_comp_add_const,
      deriv_comp_const_sub]
  rw [hderiv]
  have h1 := hC (t + (L + 1))
  have h2 := hC ((L + 1) - t)
  have h3 := Real.smoothTransition.nonneg (t + (L + 1))
  have h4 := Real.smoothTransition.le_one (t + (L + 1))
  have h5 := Real.smoothTransition.nonneg ((L + 1) - t)
  have h6 := Real.smoothTransition.le_one ((L + 1) - t)
  calc |deriv Real.smoothTransition (t + (L + 1)) * Real.smoothTransition ((L + 1) - t) +
        Real.smoothTransition (t + (L + 1)) * -deriv Real.smoothTransition ((L + 1) - t)|
      ≤ |deriv Real.smoothTransition (t + (L + 1))| * |Real.smoothTransition ((L + 1) - t)| +
        |Real.smoothTransition (t + (L + 1))| * |deriv Real.smoothTransition ((L + 1) - t)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_neg]
    _ ≤ C * 1 + 1 * C := by
        rw [abs_of_nonneg h3, abs_of_nonneg h5]
        gcongr
    _ = 2 * C := by ring

/-- The integrand of the radial argument: `2 v² - (α v + v')²`. -/
def bracket (α L t : ℝ) : ℝ := 2 * plateau L t ^ 2 - (α * plateau L t + deriv (plateau L) t) ^ 2

/-- Lower bound of the radial integrand by indicators of unit intervals: it is at least `1` on
`[-L+1, L-1)` and at least `-(|α| + C)²` on the four end layers. -/
theorem bracket_ge {α : ℝ} (hα : α ^ 2 ≤ 1) {C : ℝ}
    (hC : ∀ L t, |deriv (plateau L) t| ≤ C) (L : ℝ) (t : ℝ) :
    (Ico (-L + 1) (L - 1)).indicator 1 t -
        (|α| + C) ^ 2 * ((Ico (-L - 1) (-L + 1)).indicator 1 t + (Ico L (L + 2)).indicator 1 t) ≤
      bracket α L t := by
  have hv0 := plateau_nonneg L t
  have hv1 := plateau_le_one L t
  have hd := hC L t
  have hsq : (α * plateau L t + deriv (plateau L) t) ^ 2 ≤ (|α| + C) ^ 2 := by
    have : |α * plateau L t + deriv (plateau L) t| ≤ |α| + C := by
      refine (abs_add_le _ _).trans (add_le_add ?_ hd)
      rw [abs_mul, abs_of_nonneg hv0]
      exact mul_le_of_le_one_right (abs_nonneg _) hv1
    exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
  have hlow : -(|α| + C) ^ 2 ≤ bracket α L t := by
    unfold bracket
    nlinarith [sq_nonneg (plateau L t)]
  have hind1 : ∀ s : Set ℝ, 0 ≤ s.indicator (1 : ℝ → ℝ) t := fun s ↦
    indicator_nonneg (fun _ _ ↦ zero_le_one) t
  have hind2 : ∀ s : Set ℝ, s.indicator (1 : ℝ → ℝ) t ≤ 1 := fun s ↦
    indicator_le_self' (fun _ _ ↦ zero_le_one) t |>.trans (le_refl _)
  by_cases hin : t ∈ Ioo (-L) L
  · -- on the plateau the integrand is `2 - α² ≥ 1`
    have hv : plateau L t = 1 := (plateau_eventually_one hin).eq_of_nhds
    have hdv : deriv (plateau L) t = 0 := by
      rw [(plateau_eventually_one hin).deriv_eq, deriv_const]
    have hb : bracket α L t = 2 - α ^ 2 := by
      unfold bracket
      rw [hv, hdv]
      ring
    have h1 := hind2 (Ico (-L + 1) (L - 1))
    have h2 := hind1 (Ico (-L - 1) (-L + 1))
    have h3 := hind1 (Ico L (L + 2))
    rw [hb]
    nlinarith [sq_nonneg (|α| + C)]
  · have hgood : (Ico (-L + 1) (L - 1)).indicator (1 : ℝ → ℝ) t = 0 := by
      refine indicator_of_notMem (fun h ↦ hin ⟨?_, ?_⟩) _
      · linarith [h.1]
      · linarith [h.2]
    by_cases hlay : t ∈ Icc (-L - 1) (L + 1)
    · -- on the end layers
      have hbad : 1 ≤ (Ico (-L - 1) (-L + 1)).indicator (1 : ℝ → ℝ) t +
          (Ico L (L + 2)).indicator (1 : ℝ → ℝ) t := by
        rcases not_and_or.mp hin with h | h
        · rw [indicator_of_mem (show t ∈ Ico (-L - 1) (-L + 1) from
            ⟨hlay.1, by linarith [not_lt.mp h]⟩), Pi.one_apply]
          linarith [hind1 (Ico L (L + 2))]
        · rw [indicator_of_mem (show t ∈ Ico L (L + 2) from
            ⟨not_lt.mp h, by linarith [hlay.2]⟩), Pi.one_apply]
          linarith [hind1 (Ico (-L - 1) (-L + 1))]
      rw [hgood]
      nlinarith [sq_nonneg (|α| + C)]
    · -- outside the support
      have hout : t < -(L + 1) ∨ L + 1 < t := by
        rcases not_and_or.mp hlay with h | h
        · left
          linarith [not_le.mp h]
        · right
          linarith [not_le.mp h]
      have hv : plateau L t = 0 := (plateau_eventually_zero hout).eq_of_nhds
      have hdv : deriv (plateau L) t = 0 := by
        rw [(plateau_eventually_zero hout).deriv_eq, deriv_const]
      have hb : bracket α L t = 0 := by
        unfold bracket
        rw [hv, hdv]
        ring
      rw [hgood, hb]
      have h2 := hind1 (Ico (-L - 1) (-L + 1))
      have h3 := hind1 (Ico L (L + 2))
      nlinarith [sq_nonneg (|α| + C)]

/-- The radial profile `φ(r) = r^α v_L(log r)` (and `0` for `r ≤ 0`). -/
def radialProfile (α L r : ℝ) : ℝ := if 0 < r then r ^ α * plateau L (Real.log r) else 0

theorem radialProfile_eq_zero {α L r : ℝ} (hr : r < Real.exp (-(L + 1)) ∨ Real.exp (L + 1) < r) :
    radialProfile α L r = 0 := by
  unfold radialProfile
  split_ifs with h0
  · rcases hr with hr | hr
    · rw [plateau_eq_zero (Or.inl ((Real.log_lt_iff_lt_exp h0).mpr hr).le), mul_zero]
    · rw [plateau_eq_zero (Or.inr ((Real.lt_log_iff_exp_lt h0).mpr hr).le), mul_zero]
  · rfl

theorem contDiff_radialProfile (α L : ℝ) : ContDiff ℝ ∞ (radialProfile α L) := by
  refine contDiff_iff_contDiffAt.mpr fun r ↦ ?_
  by_cases hr : 0 < r
  · have hev : radialProfile α L =ᶠ[𝓝 r] fun r ↦ r ^ α * plateau L (Real.log r) := by
      filter_upwards [Ioi_mem_nhds hr] with s hs
      simp [radialProfile, show 0 < s from hs]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (Real.contDiffAt_rpow_const_of_ne hr.ne').mul
      ((contDiff_plateau L).contDiffAt.comp r (Real.contDiffAt_log.mpr hr.ne'))
  · have hev : radialProfile α L =ᶠ[𝓝 r] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds ((not_lt.mp hr).trans_lt (Real.exp_pos (-(L + 1))))]
        with s hs
      exact radialProfile_eq_zero (Or.inl hs)
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem hasDerivAt_radialProfile (α L : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (radialProfile α L)
      (r ^ (α - 1) * (α * plateau L (Real.log r) + deriv (plateau L) (Real.log r))) r := by
  have hev : radialProfile α L =ᶠ[𝓝 r] fun r ↦ r ^ α * plateau L (Real.log r) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    simp [radialProfile, show 0 < s from hs]
  have h1 : HasDerivAt (fun r : ℝ ↦ r ^ α) (α * r ^ (α - 1)) r :=
    Real.hasDerivAt_rpow_const (Or.inl hr.ne')
  have h2 : HasDerivAt (fun r ↦ plateau L (Real.log r))
      (deriv (plateau L) (Real.log r) * r⁻¹) r :=
    ((contDiff_plateau L).differentiable (by simp) _).hasDerivAt.comp r
      (Real.hasDerivAt_log hr.ne')
  have h3 := (h1.mul h2).congr_of_eventuallyEq hev
  convert h3 using 1
  rw [Real.rpow_sub_one hr.ne']
  field_simp

/-- The radial integrand: `2 φ²/r² - φ'² = (r^{α-1})² (2 v² - (α v + v')²)` at `r > 0`. -/
theorem radialProfile_identity (α L : ℝ) {r : ℝ} (hr : 0 < r) :
    2 * (radialProfile α L r ^ 2 / r ^ 2) - deriv (radialProfile α L) r ^ 2 =
      (r ^ (α - 1)) ^ 2 * bracket α L (Real.log r) := by
  rw [(hasDerivAt_radialProfile α L hr).deriv]
  have hφ : radialProfile α L r = r ^ α * plateau L (Real.log r) := by
    simp [radialProfile, hr]
  have hrα : r ^ α = r ^ (α - 1) * r := by
    rw [Real.rpow_sub_one hr.ne']
    field_simp
  rw [hφ, hrα, bracket]
  field_simp

end Profile


/-! ### 2. Dilations of the perimeter measure of a cone -/

section Scaling

variable {m : ℕ}

/-- **Scaling of the perimeter measure of a cone.** If `μ` represents the perimeter of an a.e.
dilation invariant set `T ⊆ ℝ^{m+1}` on open sets, then `μ (s⁻¹ U) = s^{-m} μ U`, i.e.
`map (s • ·) μ = s^{-m} μ`. -/
theorem map_smul_perimeterMeasure {T : Set (Space (m + 1))}
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ T ↔ a • x ∈ T)
    {μ : Measure (Space (m + 1))} [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U →
      μ U = variationalPerimeter (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) T U)
    {s : ℝ} (hs : 0 < s) :
    Measure.map (fun x ↦ s • x) μ = ENNReal.ofReal ((s ^ m)⁻¹) • μ := by
  have hcont : Continuous (fun x : Space (m + 1) ↦ s • x) := continuous_const_smul s
  have hmeas : Measurable (fun x : Space (m + 1) ↦ s • x) := hcont.measurable
  refine Measure.ext_of_generateFrom_of_iUnion {U | IsOpen U}
    (fun n : ℕ ↦ ball (0 : Space (m + 1)) ((n : ℝ) + 1)) BorelSpace.measurable_eq
    isPiSystem_isOpen (iUnion_ball_nat_succ 0) (fun n ↦ show IsOpen (ball (0 : Space (m + 1)) ((n : ℝ) + 1)) from isOpen_ball)
    (fun n ↦ ?_)
    (fun U hU ↦ ?_)
  · rw [Measure.map_apply hmeas measurableSet_ball]
    have hsub : (fun x : Space (m + 1) ↦ s • x) ⁻¹' ball 0 ((n : ℝ) + 1) ⊆
        closedBall 0 (((n : ℝ) + 1) / s) := by
      intro x hx
      simp only [mem_preimage, mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg hs.le] at hx
      rw [mem_closedBall, dist_zero_right, le_div_iff₀ hs]
      linarith
    exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne
  · have hU0 : IsOpen U := hU
    have hU' : IsOpen ((fun x : Space (m + 1) ↦ s • x) ⁻¹' U) := hU0.preimage hcont
    rw [Measure.map_apply hmeas hU0.measurableSet, Measure.smul_apply, hμ _ hU', hμ U hU0,
      smul_eq_mul]
    have hae : T =ᵐ[volume] (fun y : Space (m + 1) ↦ s • y) ⁻¹' T := by
      filter_upwards [hcone s hs] with y hy
      exact propext hy
    rw [variationalPerimeter_congr_ae _ hae]
    have h := variationalPerimeter_preimage_add_smul (by omega : 1 ≤ m + 1)
      (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) T U 0 hs
    simp only [zero_add, Nat.add_sub_cancel] at h
    exact h

/-- Change of variables for the perimeter measure of a cone:
`∫ f (s • y) dμ(y) = s^{-m} ∫ f dμ`. -/
theorem integral_comp_smul_perimeterMeasure {T : Set (Space (m + 1))}
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ T ↔ a • x ∈ T)
    {μ : Measure (Space (m + 1))} [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U →
      μ U = variationalPerimeter (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) T U)
    {s : ℝ} (hs : 0 < s) {f : Space (m + 1) → ℝ} (hf : AEStronglyMeasurable f μ) :
    ∫ y, f (s • y) ∂μ = (s ^ m)⁻¹ * ∫ x, f x ∂μ := by
  have hmap := map_smul_perimeterMeasure hcone hμ hs
  have hmeas : AEMeasurable (fun x : Space (m + 1) ↦ s • x) μ :=
    (continuous_const_smul s).measurable.aemeasurable
  rw [← integral_map hmeas (by rw [hmap]; exact hf.smul_measure _), hmap,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

end Scaling

/-! ### 3. The cone functional -/

section Functional

variable {m : ℕ} {T V : Set (Space (m + 1))} {F : Space (m + 1) → ℝ}
  {μ : Measure (Space (m + 1))}

theorem continuousOn_weight (h : IsSmoothBoundaryChart T V F)
    (hV0 : (0 : Space (m + 1)) ∉ V) (p : ℝ) :
    ContinuousOn (fun x ↦ sqNormSecondFundamentalForm F x * ‖x‖ ^ p) V :=
  h.contDiffOn_sqNormSecondFundamentalForm.continuousOn.mul
    (continuous_norm.continuousOn.rpow_const fun _x hx ↦
      Or.inl (norm_ne_zero_iff.mpr fun h0 ↦ hV0 (h0 ▸ hx)))

theorem aestronglyMeasurable_weight (h : IsSmoothBoundaryChart T V F)
    (hV0 : (0 : Space (m + 1)) ∉ V) (p : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    AEStronglyMeasurable (fun x ↦ sqNormSecondFundamentalForm F x * ‖x‖ ^ p *
      g (Real.log ‖x‖)) (μ.restrict V) :=
  ((continuousOn_weight h hV0 p).aestronglyMeasurable h.isOpen.measurableSet).mul
    (hg.comp (Real.measurable_log.comp measurable_norm)).aestronglyMeasurable

/-- Integrability of the cone functional for bounded measurable profiles supported in a range of
radii on which the boundary lies in the chart. -/
theorem integrable_weight [IsFiniteMeasure (μ.restrict V)] (h : IsSmoothBoundaryChart T V F)
    (hV0 : (0 : Space (m + 1)) ∉ V) {lo hi : ℝ}
    (hKc : IsCompact (measureTheoreticBoundary T ∩ {x | Real.exp lo ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp hi}))
    (hK : measureTheoreticBoundary T ∩ {x | Real.exp lo ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp hi} ⊆ V)
    (hae : ∀ᵐ x ∂μ.restrict V, F x = 0) (p : ℝ) {g : ℝ → ℝ} (hg : Measurable g) {B : ℝ}
    (hgB : ∀ t, |g t| ≤ B) (hgs : ∀ t, g t ≠ 0 → t ∈ Icc lo hi) :
    Integrable (fun x ↦ sqNormSecondFundamentalForm F x * ‖x‖ ^ p * g (Real.log ‖x‖))
      (μ.restrict V) := by
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn ((continuousOn_weight h hV0 p).mono hK)
  refine Integrable.of_bound (aestronglyMeasurable_weight h hV0 p hg) (max (C * B) 0) ?_
  filter_upwards [hae, ae_restrict_mem h.isOpen.measurableSet] with x hFx hxV
  by_cases hgx : g (Real.log ‖x‖) = 0
  · simp [hgx]
  · have hx0 : x ≠ 0 := fun h0 ↦ hV0 (h0 ▸ hxV)
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hr := hgs _ hgx
    have hx1 : Real.exp lo ≤ ‖x‖ := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.mpr hr.1
    have hx2 : ‖x‖ ≤ Real.exp hi := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.mpr hr.2
    have hxK : x ∈ measureTheoreticBoundary T ∩ {x | Real.exp lo ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp hi} :=
      ⟨h.mem_measureTheoreticBoundary hxV hFx,
        (⟨hx1, hx2⟩ : Real.exp lo ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp hi)⟩
    have h1 := hC x hxK
    rw [Real.norm_eq_abs] at h1 ⊢
    rw [abs_mul]
    refine le_trans ?_ (le_max_left _ _)
    exact mul_le_mul h1 (hgB _) (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- **Translation invariance of the cone functional** under integer shifts of the profile. -/
theorem translate_eq (hT : IsMinimizingCone T) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U →
      μ U = variationalPerimeter (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) T U)
    (h : IsSmoothBoundaryChart T V F) (hV0 : (0 : Space (m + 1)) ∉ V) {lo hi : ℝ}
    (hK : measureTheoreticBoundary T ∩ {x | Real.exp lo ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp hi} ⊆ V)
    {g : ℝ → ℝ} (hg : Measurable g) {a b : ℝ} (hgs : ∀ t, g t ≠ 0 → t ∈ Icc a b) (j : ℤ)
    (hlo : lo ≤ a) (hhi : b ≤ hi) (hlo' : lo ≤ a + j) (hhi' : b + j ≤ hi) :
    ∫ x in V, sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) * g (Real.log ‖x‖ - j) ∂μ =
      ∫ x in V, sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) * g (Real.log ‖x‖) ∂μ := by
  set B := measureTheoreticBoundary T with hBdef
  have hBmeas : MeasurableSet B := (isClosed_measureTheoreticBoundary T).measurableSet
  have hnull : μ Bᶜ = 0 := by
    have := hT.minimizer.measure_sdiff_boundary_eq_zero μ (fun U hU _ ↦ hμ U hU)
    have hc : Bᶜ = univ \ measureTheoreticBoundary T := by
      ext x
      simp [hBdef]
    rwa [hc]
  have hconv : ∀ f : Space (m + 1) → ℝ,
      ∫ x in V, f x ∂μ = ∫ x, (B ∩ V).indicator f x ∂μ := by
    intro f
    rw [← integral_indicator h.isOpen.measurableSet]
    refine integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    have hxB : x ∈ B := not_not.mp hx
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem hxV, indicator_of_mem (show x ∈ B ∩ V from ⟨hxB, hxV⟩)]
    · rw [indicator_of_notMem hxV, indicator_of_notMem fun h' ↦ hxV h'.2]
  set s : ℝ := Real.exp j with hsdef
  have hs : 0 < s := Real.exp_pos _
  set f₀ : Space (m + 1) → ℝ := fun x ↦
    sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) * g (Real.log ‖x‖) with hf₀
  set fj : Space (m + 1) → ℝ := fun x ↦
    sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) * g (Real.log ‖x‖ - j) with hfj
  have hmeasj : AEStronglyMeasurable ((B ∩ V).indicator fj) μ := by
    rw [aestronglyMeasurable_indicator_iff (hBmeas.inter h.isOpen.measurableSet)]
    have := aestronglyMeasurable_weight (μ := μ) h hV0 (2 - m : ℝ)
      (g := fun t ↦ g (t - j)) (hg.comp (measurable_id.sub_const _))
    exact this.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  -- the pointwise identity under the dilation
  have hpt : ∀ y, (B ∩ V).indicator fj (s • y) = (s ^ m)⁻¹ * (B ∩ V).indicator f₀ y := by
    intro y
    by_cases hy0 : y = 0
    · subst hy0
      rw [smul_zero, indicator_of_notMem (fun h' ↦ hV0 h'.2), indicator_of_notMem
        (fun h' ↦ hV0 h'.2), mul_zero]
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hnorm : ‖s • y‖ = s * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
    have hlog : Real.log ‖s • y‖ - j = Real.log ‖y‖ := by
      rw [hnorm, Real.log_mul hs.ne' hypos.ne', hsdef, Real.log_exp]
      ring
    by_cases hyB : y ∈ B
    · have hsyB : s • y ∈ B := (hT.smul_mem_measureTheoreticBoundary_iff hs y).mpr hyB
      by_cases hgy : g (Real.log ‖y‖) = 0
      · have h1 : (B ∩ V).indicator fj (s • y) = 0 := by
          by_cases hm : s • y ∈ B ∩ V
          · rw [indicator_of_mem hm, hfj]
            simp only
            rw [hlog, hgy, mul_zero]
          · exact indicator_of_notMem hm _
        have h2 : (B ∩ V).indicator f₀ y = 0 := by
          by_cases hm : y ∈ B ∩ V
          · rw [indicator_of_mem hm, hf₀]
            simp only
            rw [hgy, mul_zero]
          · exact indicator_of_notMem hm _
        rw [h1, h2, mul_zero]
      · have hr := hgs _ hgy
        have hy1 : Real.exp lo ≤ ‖y‖ := by
          rw [← Real.exp_log hypos]
          exact Real.exp_le_exp.mpr (hlo.trans hr.1)
        have hy2 : ‖y‖ ≤ Real.exp hi := by
          rw [← Real.exp_log hypos]
          exact Real.exp_le_exp.mpr (hr.2.trans hhi)
        have hyV : y ∈ V := hK ⟨hyB, (⟨hy1, hy2⟩ : Real.exp lo ≤ ‖y‖ ∧ ‖y‖ ≤ Real.exp hi)⟩
        have hsy : Real.log ‖s • y‖ = Real.log ‖y‖ + j := by linarith [hlog]
        have hsypos : 0 < ‖s • y‖ := by rw [hnorm]; positivity
        have hsy1 : Real.exp lo ≤ ‖s • y‖ := by
          rw [← Real.exp_log hsypos, hsy]
          exact Real.exp_le_exp.mpr (by linarith [hr.1])
        have hsy2 : ‖s • y‖ ≤ Real.exp hi := by
          rw [← Real.exp_log hsypos, hsy]
          exact Real.exp_le_exp.mpr (by linarith [hr.2])
        have hsyV : s • y ∈ V :=
          hK ⟨hsyB, (⟨hsy1, hsy2⟩ : Real.exp lo ≤ ‖s • y‖ ∧ ‖s • y‖ ≤ Real.exp hi)⟩
        have hFy : F y = 0 := h.eq_zero_of_mem_measureTheoreticBoundary hyV hyB
        have hhom := homog_sqNormSecondFundamentalForm h hT.dilation hs hyV hsyV hFy
        rw [indicator_of_mem (show s • y ∈ B ∩ V from ⟨hsyB, hsyV⟩),
          indicator_of_mem (show y ∈ B ∩ V from ⟨hyB, hyV⟩), hfj, hf₀]
        simp only
        rw [hlog, hnorm, Real.mul_rpow hs.le hypos.le, hhom]
        have hsp : s ^ (2 - m : ℝ) = s ^ 2 / s ^ m := by
          rw [Real.rpow_sub hs, Real.rpow_two, Real.rpow_natCast]
        rw [hsp]
        field_simp
    · have hsyB : s • y ∉ B := fun h' ↦ hyB ((hT.smul_mem_measureTheoreticBoundary_iff hs y).mp h')
      rw [indicator_of_notMem (fun h' ↦ hsyB h'.1), indicator_of_notMem (fun h' ↦ hyB h'.1),
        mul_zero]
  have hchange := integral_comp_smul_perimeterMeasure hT.dilation hμ hs hmeasj
  rw [show (fun y ↦ (B ∩ V).indicator fj (s • y)) = fun y ↦ (s ^ m)⁻¹ *
    (B ∩ V).indicator f₀ y from funext hpt, integral_const_mul] at hchange
  rw [hconv fj, hconv f₀]
  have hsm : (s ^ m)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hs.ne')
  exact (mul_left_cancel₀ hsm hchange).symm

end Functional


/-! ### 4. Vanishing of the second fundamental form -/

section Vanishing

variable {m : ℕ}

theorem indicator_Ico_sub (c : ℤ) (t : ℝ) :
    (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (t - c) = (Ico (c : ℝ) (c + 1)).indicator 1 t := by
  by_cases ht : t ∈ Ico (c : ℝ) (c + 1)
  · rw [indicator_of_mem ht, indicator_of_mem (show t - c ∈ Ico (0 : ℝ) 1 from
      ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
    simp
  · rw [indicator_of_notMem ht, indicator_of_notMem (show t - c ∉ Ico (0 : ℝ) 1 from
      fun h ↦ ht ⟨by linarith [h.1], by linarith [h.2]⟩)]

theorem indicator_Ico_add (a : ℝ) (n : ℕ) (t : ℝ) :
    (Ico a (a + (n + 1 : ℕ))).indicator (1 : ℝ → ℝ) t =
      (Ico a (a + n)).indicator 1 t + (Ico (a + n) (a + n + 1)).indicator 1 t := by
  push_cast
  by_cases h1 : t ∈ Ico a (a + n)
  · rw [indicator_of_mem h1, indicator_of_mem (show t ∈ Ico a (a + (n + 1)) from
      ⟨h1.1, by linarith [h1.2]⟩), indicator_of_notMem (show t ∉ Ico (a + n) (a + n + 1) from
      fun h ↦ by linarith [h.1, h1.2]), add_zero]
  · by_cases h2 : t ∈ Ico (a + n) (a + n + 1)
    · rw [indicator_of_notMem h1, indicator_of_mem h2, indicator_of_mem (show t ∈ Ico a
        (a + (n + 1)) from ⟨by linarith [h2.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)],
          by linarith [h2.2]⟩), zero_add]
    · rw [indicator_of_notMem h1, indicator_of_notMem h2, indicator_of_notMem
        (show t ∉ Ico a (a + (n + 1)) from fun h ↦ by
          rcases lt_or_ge t (a + n) with h3 | h3
          · exact h1 ⟨h.1, h3⟩
          · exact h2 ⟨h3, by linarith [h.2]⟩), add_zero]

/-- **Vanishing of the second fundamental form.** Let `T ⊆ ℝ^{m+1}`, `2 ≤ m ≤ 6`, be a minimizing
cone all of whose nonzero boundary points lie in smooth boundary charts. Then the second
fundamental form of every chart vanishes at every nonzero boundary point. -/
theorem secondFundamentalForm_eq_zero_of_cone (hm2 : 2 ≤ m) (hm6 : m ≤ 6)
    {T : Set (Space (m + 1))} (hT : IsMinimizingCone T)
    (hchart : ∀ x ∈ measureTheoreticBoundary T, x ≠ 0 →
      ∃ (U : Set (Space (m + 1))) (F : Space (m + 1) → ℝ), x ∈ U ∧ IsSmoothBoundaryChart T U F)
    {U : Set (Space (m + 1))} {G : Space (m + 1) → ℝ} (hG : IsSmoothBoundaryChart T U G)
    {z : Space (m + 1)} (hzU : z ∈ U) (hGz : G z = 0) (hz0 : z ≠ 0) :
    secondFundamentalForm G z = 0 := by
  classical
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  -- constants of the radial argument
  set α : ℝ := (4 - m) / 2 with hαdef
  have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hm6' : (m : ℝ) ≤ 6 := by exact_mod_cast hm6
  have hα : α ^ 2 ≤ 1 := by
    rw [hαdef]
    nlinarith
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_plateau
  set C₁ : ℝ := (|α| + C) ^ 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := sq_nonneg _
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * C₁ + 2)
  set Lr : ℝ := (L : ℝ) with hLr
  have hL2 : 2 < Lr := by linarith
  have hL3 : 2 < L := by
    have h : (2 : ℝ) < (L : ℝ) := hL2
    exact_mod_cast h
  -- the compact part of the boundary and a chart containing it
  set K := measureTheoreticBoundary T ∩
    {x : Space (m + 1) | Real.exp (-Lr - 1) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp (Lr + 2)} with hKdef
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Space (m + 1)) (Real.exp (Lr + 2))).of_isClosed_subset ?_ ?_
    · exact (isClosed_measureTheoreticBoundary T).inter
        ((isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const))
    · intro x hx
      rw [mem_closedBall, dist_zero_right]
      exact hx.2.2
  have hK0 : ∀ x ∈ K, x ≠ 0 := fun x hx h0 ↦ by
    have h1 := hx.2.1
    rw [h0, norm_zero] at h1
    exact absurd h1 (not_le.mpr (Real.exp_pos _))
  obtain ⟨V₀, F, hKV₀, hF₀⟩ := exists_isSmoothBoundaryChart_superset hKc inter_subset_left
    (fun x hx ↦ hchart x hx.1 (hK0 x hx))
  set V := V₀ ∩ {x : Space (m + 1) | Real.exp (-Lr - 2) < ‖x‖ ∧ ‖x‖ < Real.exp (Lr + 3)}
    with hVdef
  have hVo : IsOpen V := hF₀.isOpen.inter ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const))
  have hF : IsSmoothBoundaryChart T V F := hF₀.mono hVo inter_subset_left
  have hKV : K ⊆ V := fun x hx ↦ ⟨hKV₀ hx, (⟨lt_of_lt_of_le
    (Real.exp_lt_exp.mpr (by linarith)) hx.2.1, lt_of_le_of_lt hx.2.2
      (Real.exp_lt_exp.mpr (by linarith))⟩ :
        Real.exp (-Lr - 2) < ‖x‖ ∧ ‖x‖ < Real.exp (Lr + 3))⟩
  have hV0 : (0 : Space (m + 1)) ∉ V := fun h0 ↦ by
    have h1 := h0.2.1
    rw [norm_zero] at h1
    exact absurd h1 (not_lt.mpr (Real.exp_pos _).le)
  set Ω := ball (0 : Space (m + 1)) (Real.exp (Lr + 3)) with hΩ
  have hVΩ : V ⊆ Ω := fun x hx ↦ mem_ball_zero_iff.mpr hx.2.2
  -- the perimeter measure and a polar representation on `Ω`
  have hP : ∀ n : ℕ, variationalPerimeter b T (ball 0 ((n : ℝ) + 1)) ≠ ⊤ := fun n ↦
    hT.minimizer.perimeter_ball_ne_top 0 _ (by positivity) (subset_univ _)
  set μ := perimeterRadonMeasure b hT.measurableSet hP with hμdef
  have hμ : ∀ U, IsOpen U → μ U = variationalPerimeter b T U := fun U hU ↦
    perimeterRadonMeasure_apply_open b hT.measurableSet hP hU
  have hPΩ : variationalPerimeter b T Ω ≠ ⊤ :=
    hT.minimizer.perimeter_ball_ne_top 0 _ (Real.exp_pos _) (subset_univ _)
  obtain ⟨ν, hp⟩ := exists_isPerimeterPolarOn_of_perimeter_measure b hT.measurableSet
    isOpen_ball hPΩ μ hμ
  have hmin : IsPerimeterMinimizingIn b T Ω :=
    hT.minimizer.isPerimeterMinimizingIn isOpen_ball (subset_univ _)
  have hfin : IsFiniteMeasure (μ.restrict V) :=
    IsSmoothBoundaryChart.isFiniteMeasure_restrict hp hVΩ
  have hae : ∀ᵐ x ∂μ.restrict V, F x = 0 := hF.ae_restrict_eq_zero hp hVΩ
  -- the cone functional `Ψ g = ∫_V |A|² |x|^{2-m} g(log |x|) dμ`
  have hint : ∀ g : ℝ → ℝ, Measurable g → ∀ B, (∀ t, |g t| ≤ B) →
      (∀ t, g t ≠ 0 → t ∈ Icc (-Lr - 1) (Lr + 2)) →
      Integrable (fun x ↦ sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
        g (Real.log ‖x‖)) (μ.restrict V) :=
    fun g hg B hgB hgs ↦ integrable_weight hF hV0 hKc hKV hae _ hg hgB hgs
  have hindm : ∀ a c : ℝ, Measurable ((Ico a c).indicator (1 : ℝ → ℝ)) := fun a c ↦
    measurable_one.indicator measurableSet_Ico
  have hindB : ∀ a c t : ℝ, |(Ico a c).indicator (1 : ℝ → ℝ) t| ≤ 1 := fun a c t ↦ by
    by_cases ht : t ∈ Ico a c
    · rw [indicator_of_mem ht, Pi.one_apply, abs_one]
    · rw [indicator_of_notMem ht, abs_zero]
      exact zero_le_one
  have hinds : ∀ a c : ℝ, -Lr - 1 ≤ a → c ≤ Lr + 2 → ∀ t,
      (Ico a c).indicator (1 : ℝ → ℝ) t ≠ 0 → t ∈ Icc (-Lr - 1) (Lr + 2) := by
    intro a c ha hc t ht
    have ht' : t ∈ Ico a c := by
      by_contra h
      exact ht (indicator_of_notMem h _)
    exact ⟨ha.trans ht'.1, ht'.2.le.trans hc⟩
  set q := ∫ x in V, sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
    (Ico (0 : ℝ) 1).indicator 1 (Real.log ‖x‖) ∂μ with hqdef
  -- translation invariance for unit intervals
  have htrans : ∀ c : ℤ, -Lr - 1 ≤ c → (c : ℝ) + 1 ≤ Lr + 2 →
      ∫ x in V, sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
        (Ico (c : ℝ) (c + 1)).indicator 1 (Real.log ‖x‖) ∂μ = q := by
    intro c hc1 hc2
    have h := translate_eq hT hμ hF hV0 hKV (hindm 0 1) (a := 0) (b := 1)
      (fun t ht ↦ hinds 0 1 (by linarith) (by linarith) t ht |> fun _ ↦ by
        have ht' : t ∈ Ico (0 : ℝ) 1 := by
          by_contra h
          exact ht (indicator_of_notMem h _)
        exact ⟨ht'.1, ht'.2.le⟩) c (by linarith) (by linarith) (by linarith) (by linarith)
    rw [hqdef, ← h]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [indicator_Ico_sub]
  -- additivity
  have hadd : ∀ n : ℕ, ∀ a : ℤ, -Lr - 1 ≤ a → (a : ℝ) + n ≤ Lr + 2 →
      ∫ x in V, sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
        (Ico (a : ℝ) (a + n)).indicator 1 (Real.log ‖x‖) ∂μ = n * q := by
    intro n
    induction n with
    | zero =>
      intro a _ _
      simp
    | succ n ih =>
      intro a ha1 ha2
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hsplit : (fun x ↦ sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
          (Ico (a : ℝ) (a + (n + 1 : ℕ))).indicator 1 (Real.log ‖x‖)) = fun x ↦
            sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
              (Ico (a : ℝ) (a + n)).indicator 1 (Real.log ‖x‖) +
            sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
              (Ico ((a + n : ℤ) : ℝ) ((a + n : ℤ) + 1)).indicator 1 (Real.log ‖x‖) := by
        funext x
        rw [indicator_Ico_add, mul_add]
        push_cast
        ring
      have h1 := hint ((Ico (a : ℝ) (a + n)).indicator 1) (hindm _ _) 1 (hindB _ _)
        (hinds (a : ℝ) ((a : ℝ) + n) ha1 (by push_cast at ha2 ⊢; linarith))
      have h2 := hint ((Ico ((a + n : ℤ) : ℝ) ((a + n : ℤ) + 1)).indicator 1) (hindm _ _) 1
        (hindB _ _) (hinds ((a + n : ℤ) : ℝ) ((a + n : ℤ) + 1)
          (by push_cast; linarith) (by push_cast at ha2 ⊢; linarith))
      rw [hsplit, integral_add h1 h2, ih a ha1 (by push_cast at ha2 ⊢; linarith),
        htrans (a + n) (by push_cast; linarith) (by push_cast at ha2 ⊢; linarith)]
      push_cast
      ring
  -- the stability inequality with the radial profile `φ(r) = r^α v_L(log r)`
  have hK' : measureTheoreticBoundary T ∩
      {x | Real.exp (-(Lr + 1)) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp (Lr + 1)} ⊆ V := by
    intro x hx
    refine hKV ⟨hx.1, (⟨(Real.exp_le_exp.mpr (by linarith)).trans hx.2.1,
      hx.2.2.trans (Real.exp_le_exp.mpr (by linarith))⟩ :
        Real.exp (-Lr - 1) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp (Lr + 2))⟩
  have hstab := integral_radial_nonpos hT.measurableSet hT.dilation hp hmin hF hVΩ
    (contDiff_radialProfile α Lr) (Real.exp_pos (-(Lr + 1)))
    (fun r hr ↦ radialProfile_eq_zero hr) hK'
  have hbr : ∫ x in V, sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
      bracket α Lr (Real.log ‖x‖) ∂μ ≤ 0 := by
    refine le_trans (le_of_eq (setIntegral_congr_fun hVo.measurableSet fun x hx ↦ ?_)) hstab
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr fun h0 ↦ hV0 (h0 ▸ hx)
    rw [radialProfile_identity α Lr hx0]
    have hpow : (‖x‖ ^ (α - 1)) ^ 2 = ‖x‖ ^ (2 - m : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      rw [hαdef]
      push_cast
      ring
    rw [hpow]
    ring
  -- integrability of the bracket term
  have hbr_meas : Measurable (bracket α Lr) := by
    have hc : Continuous (bracket α Lr) := by
      unfold bracket
      have h1 := (contDiff_plateau Lr).continuous
      have h2 := (contDiff_plateau Lr).continuous_deriv (by simp)
      fun_prop
    exact hc.measurable
  have hbr_bound : ∀ t, |bracket α Lr t| ≤ 2 + C₁ := by
    intro t
    have hv0 := plateau_nonneg Lr t
    have hv1 := plateau_le_one Lr t
    have hsq : (α * plateau Lr t + deriv (plateau Lr) t) ^ 2 ≤ C₁ := by
      have : |α * plateau Lr t + deriv (plateau Lr) t| ≤ |α| + C := by
        refine (abs_add_le _ _).trans (add_le_add ?_ (hC Lr t))
        rw [abs_mul, abs_of_nonneg hv0]
        exact mul_le_of_le_one_right (abs_nonneg _) hv1
      exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
    unfold bracket
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (α * plateau Lr t + deriv (plateau Lr) t)]
  have hbr_supp : ∀ t, bracket α Lr t ≠ 0 → t ∈ Icc (-Lr - 1) (Lr + 2) := by
    intro t ht
    by_contra hout
    apply ht
    have hout' : t < -(Lr + 1) ∨ Lr + 1 < t := by
      rcases not_and_or.mp hout with h | h
      · left
        linarith [not_le.mp h]
      · right
        linarith [not_le.mp h]
    unfold bracket
    rw [(plateau_eventually_zero hout').eq_of_nhds, (plateau_eventually_zero hout').deriv_eq,
      deriv_const]
    ring
  have hintbr := hint _ hbr_meas _ hbr_bound hbr_supp
  -- the indicator lower bound, integrated
  have hlow : ∫ x in V, sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
      ((Ico (-Lr + 1) (Lr - 1)).indicator 1 (Real.log ‖x‖) - C₁ *
        ((Ico (-Lr - 1) (-Lr + 1)).indicator 1 (Real.log ‖x‖) +
          (Ico Lr (Lr + 2)).indicator 1 (Real.log ‖x‖))) ∂μ ≤ 0 := by
    refine le_trans (integral_mono ?_ hintbr fun x ↦ ?_) hbr
    · have h1 := hint _ (hindm (-Lr + 1) (Lr - 1)) 1 (hindB _ _)
        (hinds _ _ (by linarith) (by linarith))
      have h2 := hint _ (hindm (-Lr - 1) (-Lr + 1)) 1 (hindB _ _)
        (hinds _ _ (by linarith) (by linarith))
      have h3 := hint _ (hindm Lr (Lr + 2)) 1 (hindB _ _)
        (hinds _ _ (by linarith) (by linarith))
      refine (h1.sub ((h2.add h3).const_mul C₁)).congr (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    · exact mul_le_mul_of_nonneg_left (bracket_ge hα hC Lr _)
        (mul_nonneg (sqNormSecondFundamentalForm_nonneg F x) (Real.rpow_nonneg (norm_nonneg x) _))
  -- evaluate the three indicator integrals by translation invariance
  have hval : ∀ (a : ℤ) (n : ℕ) (lo hi : ℝ), (a : ℝ) = lo → (a : ℝ) + n = hi →
      -Lr - 1 ≤ a → (a : ℝ) + n ≤ Lr + 2 →
      ∫ x in V, sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
        (Ico lo hi).indicator 1 (Real.log ‖x‖) ∂μ = n * q := by
    intro a n lo hi hlo hhi h1 h2
    rw [← hlo, ← hhi]
    exact hadd n a h1 h2
  have hgood := hval (-(L : ℤ) + 1) (2 * L - 2) (-Lr + 1) (Lr - 1) (by push_cast; ring)
    (by push_cast [Nat.cast_sub (show 2 ≤ 2 * L by omega)]; ring) (by push_cast; linarith)
    (by push_cast [Nat.cast_sub (show 2 ≤ 2 * L by omega)]; linarith)
  have hbad1 := hval (-(L : ℤ) - 1) 2 (-Lr - 1) (-Lr + 1) (by push_cast; ring)
    (by push_cast; ring) (by push_cast; linarith) (by push_cast; linarith)
  have hbad2 := hval (L : ℤ) 2 Lr (Lr + 2) (by push_cast; ring) (by push_cast; ring)
    (by push_cast; linarith) (by push_cast; linarith)
  have h1 := hint _ (hindm (-Lr + 1) (Lr - 1)) 1 (hindB _ _) (hinds _ _ (by linarith) (by linarith))
  have h2 := hint _ (hindm (-Lr - 1) (-Lr + 1)) 1 (hindB _ _)
    (hinds _ _ (by linarith) (by linarith))
  have h3 := hint _ (hindm Lr (Lr + 2)) 1 (hindB _ _) (hinds _ _ (by linarith) (by linarith))
  have hsplit : (fun x ↦ sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
      ((Ico (-Lr + 1) (Lr - 1)).indicator 1 (Real.log ‖x‖) - C₁ *
        ((Ico (-Lr - 1) (-Lr + 1)).indicator 1 (Real.log ‖x‖) +
          (Ico Lr (Lr + 2)).indicator 1 (Real.log ‖x‖)))) = fun x ↦
      sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
        (Ico (-Lr + 1) (Lr - 1)).indicator 1 (Real.log ‖x‖) - C₁ *
      (sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
        (Ico (-Lr - 1) (-Lr + 1)).indicator 1 (Real.log ‖x‖) +
      sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
        (Ico Lr (Lr + 2)).indicator 1 (Real.log ‖x‖)) := by
    funext x
    ring
  have h23 : Integrable (fun x ↦ C₁ *
      (sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
        (Ico (-Lr - 1) (-Lr + 1)).indicator 1 (Real.log ‖x‖) +
      sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
        (Ico Lr (Lr + 2)).indicator 1 (Real.log ‖x‖))) (μ.restrict V) :=
    (h2.add h3).const_mul C₁
  rw [hsplit, integral_sub h1 h23, integral_const_mul, integral_add h2 h3, hgood, hbad1,
    hbad2] at hlow
  have hq0' : 0 ≤ q := integral_nonneg fun x ↦ mul_nonneg (mul_nonneg
    (sqNormSecondFundamentalForm_nonneg F x) (Real.rpow_nonneg (norm_nonneg x) _))
      (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  have hcast : ((2 * L - 2 : ℕ) : ℝ) = 2 * Lr - 2 := by
    push_cast [Nat.cast_sub (show 2 ≤ 2 * L by omega)]
    ring
  rw [hcast] at hlow
  have hq0 : q = 0 := by
    have hcoef : 0 < 2 * Lr - 2 - 4 * C₁ := by linarith
    push_cast at hlow
    nlinarith
  -- vanishing of `|A|²` on the shell `1 < |x| < e`
  have hint0 := hint _ (hindm 0 1) 1 (hindB 0 1) (hinds 0 1 (by linarith) (by linarith))
  have hzero_ae := (integral_eq_zero_iff_of_nonneg (fun x ↦ mul_nonneg (mul_nonneg
    (sqNormSecondFundamentalForm_nonneg F x) (Real.rpow_nonneg (norm_nonneg x) _))
      (indicator_nonneg (fun _ _ ↦ zero_le_one) _)) hint0).mp hq0
  have hshell : ∀ y ∈ V, F y = 0 → 1 < ‖y‖ → ‖y‖ < Real.exp 1 →
      sqNormSecondFundamentalForm F y = 0 := by
    intro y hyV hFy hy1 hy2
    by_contra hne
    have hapos : 0 < sqNormSecondFundamentalForm F y :=
      lt_of_le_of_ne (sqNormSecondFundamentalForm_nonneg F y) (Ne.symm hne)
    have hcA : ContinuousAt (sqNormSecondFundamentalForm F) y :=
      hF.contDiffOn_sqNormSecondFundamentalForm.continuousOn.continuousAt (hVo.mem_nhds hyV)
    have e1 : ∀ᶠ x in 𝓝 y, x ∈ V := hVo.mem_nhds hyV
    have e2 : ∀ᶠ x in 𝓝 y, 0 < sqNormSecondFundamentalForm F x := hcA.eventually (lt_mem_nhds hapos)
    have e3 : ∀ᶠ x in 𝓝 y, 1 < ‖x‖ := continuous_norm.continuousAt.eventually (lt_mem_nhds hy1)
    have e4 : ∀ᶠ x in 𝓝 y, ‖x‖ < Real.exp 1 :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds hy2)
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (e1.and (e2.and (e3.and e4)))
    have hpos := hF.measure_ball_pos hT.measurableSet hp hVΩ hyV hFy hρ
    have hnull : μ.restrict V (ball y ρ) = 0 := by
      refine measure_mono_null (fun x hx ↦ ?_) (ae_iff.mp hzero_ae)
      obtain ⟨_, hax, hx1, hx2⟩ := hball x hx
      have hlog : Real.log ‖x‖ ∈ Ico (0 : ℝ) 1 :=
        ⟨Real.log_nonneg hx1.le, (Real.log_lt_iff_lt_exp (by linarith)).mpr hx2⟩
      show ¬ (sqNormSecondFundamentalForm F x * ‖x‖ ^ (2 - m : ℝ) *
        (Ico (0 : ℝ) 1).indicator 1 (Real.log ‖x‖) = (0 : Space (m + 1) → ℝ) x)
      rw [indicator_of_mem hlog, Pi.one_apply, mul_one, Pi.zero_apply]
      exact (mul_pos hax (Real.rpow_pos_of_pos (by linarith) _)).ne'
    exact hpos.ne' hnull
  -- transport to the given point by a dilation
  have hzB : z ∈ measureTheoreticBoundary T := hG.mem_measureTheoreticBoundary hzU hGz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set s : ℝ := Real.exp (1 / 2) / ‖z‖ with hsdef
  have hs : 0 < s := div_pos (Real.exp_pos _) hzpos
  have hsz : ‖s • z‖ = Real.exp (1 / 2) := by
    rw [norm_smul, Real.norm_of_nonneg hs.le, hsdef, div_mul_cancel₀ _ hzpos.ne']
  have hszB : s • z ∈ measureTheoreticBoundary T :=
    (hT.smul_mem_measureTheoreticBoundary_iff hs z).mpr hzB
  have hszK : s • z ∈ K := ⟨hszB, (⟨by rw [hsz]; exact Real.exp_le_exp.mpr (by linarith),
    by rw [hsz]; exact Real.exp_le_exp.mpr (by linarith)⟩ :
      Real.exp (-Lr - 1) ≤ ‖s • z‖ ∧ ‖s • z‖ ≤ Real.exp (Lr + 2))⟩
  have hszV := hKV hszK
  have hFsz : F (s • z) = 0 := hF.eq_zero_of_mem_measureTheoreticBoundary hszV hszB
  have ha0 : sqNormSecondFundamentalForm F (s • z) = 0 := by
    refine hshell _ hszV hFsz ?_ ?_
    · rw [hsz, ← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    · rw [hsz]
      exact Real.exp_lt_exp.mpr (by norm_num)
  have hA0 : secondFundamentalForm F (s • z) = 0 :=
    hF.secondFundamentalForm_eq_zero_of_sqNorm_eq_zero hszV ha0
  have hdil := chart_dilate hF hT.dilation hs
  have hcomp : secondFundamentalForm (fun y ↦ F (s • y)) z = 0 := by
    rw [secondFundamentalForm_comp_smul hF hs hszV, hA0]
    ext1 v
    simp
  have hcompat := hG.secondFundamentalForm_eq_of_mem_boundary hdil hzU hszV hzB
  rw [hcomp] at hcompat
  exact hcompat.symm

end Vanishing

end Simons

end SerrinEpigraph
