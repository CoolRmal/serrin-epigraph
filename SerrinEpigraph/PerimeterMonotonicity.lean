module

public import SerrinEpigraph.LocalPerimeterMinimizer
public import SerrinEpigraph.MinimizerDensity
public import SerrinEpigraph.MinimizerCompactness
public import SerrinEpigraph.PerimeterVariation
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Norm
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Perimeter Monotonicity Formula, Cone Rigidity, and Minimal Tangent/Blowdown Cones (BV10–BV11)

For local perimeter minimizers (`IsLocalPerimeterMinimizer b E Ω`) in `Space (m + 1)` for all
`m : ℕ` (including `m = 0`), this module proves:
1. **Radial first variation identity (BV10.1)**: plugging smooth radial vector fields
   `X(x) = η ‖x - x₀‖ • (x - x₀)` (constant near `0`, compactly supported in `ball x₀ R₀`) into
   the `C²` first variation formula yields the radial stationarity identity.
2. **Exact perimeter monotonicity formula and density limits (BV10.2)**: via a smooth nonincreasing
   cutoff and 1D radial antiderivative kernel that eliminates singular endpoint behavior at `x₀`,
   `R ^ (-m) * μ.real (ball x₀ R) - r ^ (-m) * μ.real (ball x₀ r)` equals
   `r ^ (-m) * μ.real (sphere x₀ r)` plus the radial tilt integral over
   `ball x₀ R \ closedBall x₀ r`. In particular, `r ↦ r ^ (-m) * P(E, ball x₀ r)` is monotone and
   admits finite positive-scale limits `perimeterDensity` (`r → 0+`) and
   `perimeterInfinityDensity` (`r → ∞`).
3. **Constant perimeter density implies cone invariance (BV10.3)**: constancy of
   `r ↦ r ^ (-m) * P(E, ball x₀ r)` forces vanishing sphere atoms, a.e. radial orthogonality
   `⟨x - x₀, ν x⟩ = 0`, `L¹_loc` scale invariance `1_E(x₀ + a • ·) =ᵐ 1_E(x₀ + ·)` for all
   `a > 0`, and strict cone invariance of `measureTheoreticInterior` and `measureTheoreticBoundary`.
4. **Existence of nontrivial minimal tangent and blowdown cones (BV11)**: along any `r_j → 0+` at
   `x₀ ∈ measureTheoreticBoundary E ∩ Ω` (respectively `R_j → ∞` when `Ω = univ`), rescaled phases
   admit a subsequence converging in `L¹_loc` to a nontrivial global perimeter-minimizing cone `C`
   whose ball perimeter satisfies `P(C, ball 0 R) = θ * R ^ m` for every `R > 0`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter ContinuousLinearMap
open scoped Topology CompactlySupported ENNReal Pointwise

namespace SerrinEpigraph

/-! ### 1. Radial First Variation Identity (BV10.1) -/

private theorem sum_apply_mul_inner_basis {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (L : Space d →L[ℝ] ℝ) (w : Space d) :
    (∑ i : Fin d, L (b i) * inner ℝ (b i) w) = L w := by
  have hw : (∑ i : Fin d, inner ℝ (b i) w • b i) = w := b.sum_repr' w
  calc
    (∑ i : Fin d, L (b i) * inner ℝ (b i) w)
      = ∑ i : Fin d, L (inner ℝ (b i) w • b i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_smul, smul_eq_mul, mul_comm]
    _ = L (∑ i : Fin d, inner ℝ (b i) w • b i) := (map_sum L _ _).symm
    _ = L w := by rw [hw]

private theorem fderiv_smul_sub_const {d : ℕ} {φ : Space d → ℝ}
    {x : Space d} (hφ : DifferentiableAt ℝ φ x) (x₀ v : Space d) :
    fderiv ℝ (fun y ↦ φ y • (y - x₀)) x v =
      φ x • v + (fderiv ℝ φ x v) • (x - x₀) := by
  have hd := hφ.hasFDerivAt.smul ((hasFDerivAt_id x).sub_const x₀)
  change HasFDerivAt (fun y ↦ φ y • (y - x₀)) _ x at hd
  rw [hd.fderiv]
  simp

private theorem fieldDivergence_smul_sub_const {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {φ : Space d → ℝ}
    {x : Space d} (hφ : DifferentiableAt ℝ φ x) (x₀ : Space d) :
    fieldDivergence b (fun y ↦ φ y • (y - x₀)) x =
      (d : ℝ) * φ x + fderiv ℝ φ x (x - x₀) := by
  unfold fieldDivergence
  simp_rw [fderiv_smul_sub_const hφ, inner_add_right, real_inner_smul_right]
  rw [Finset.sum_add_distrib, sum_apply_mul_inner_basis b (fderiv ℝ φ x) (x - x₀)]
  simp

/-- A `C²` scalar profile `η : ℝ → ℝ` that is constant near `0` defines a `C²` radial scalar
function `x ↦ η ‖x - x₀‖` on all of `Space d`. -/
theorem contDiff_comp_norm_sub {d : ℕ} {η : ℝ → ℝ} (hη : ContDiff ℝ 2 η)
    (x₀ : Space d) (hconst : ∃ ε > 0, ∀ s, |s| < ε → η s = η 0) :
    ContDiff ℝ 2 (fun x ↦ η ‖x - x₀‖) := by
  obtain ⟨ε, hε, hε_eq⟩ := hconst
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = x₀
  · subst hx
    refine (contDiffAt_const (c := η 0)).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds x hε] with y hy
    have hnorm : |‖y - x‖| < ε := by
      rw [abs_of_nonneg (norm_nonneg _)]
      simpa [mem_ball, dist_eq_norm] using hy
    exact hε_eq ‖y - x‖ hnorm
  · exact hη.contDiffAt.comp x ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hx))

/-- A `C²` scalar profile `η : ℝ → ℝ` that is constant near `0` defines a `C²` radial vector field
`x ↦ η ‖x - x₀‖ • (x - x₀)` on all of `Space d`. -/
theorem contDiff_radialVectorField {d : ℕ} {η : ℝ → ℝ} (hη : ContDiff ℝ 2 η)
    (x₀ : Space d) (hconst : ∃ ε > 0, ∀ s, |s| < ε → η s = η 0) :
    ContDiff ℝ 2 (fun x ↦ η ‖x - x₀‖ • (x - x₀)) :=
  (contDiff_comp_norm_sub hη x₀ hconst).smul (contDiff_id.sub contDiff_const)

/-- If `tsupport η ⊆ Iio R₀`, then the radial vector field `x ↦ η ‖x - x₀‖ • (x - x₀)` has
topological support contained in `ball x₀ R₀`. -/
theorem tsupport_radialVectorField_subset {d : ℕ} {η : ℝ → ℝ} (x₀ : Space d) {R₀ : ℝ}
    (hts : tsupport η ⊆ Iio R₀) :
    tsupport (fun x ↦ η ‖x - x₀‖ • (x - x₀)) ⊆ ball x₀ R₀ := by
  have h1 : tsupport (fun x ↦ η ‖x - x₀‖ • (x - x₀)) ⊆ tsupport (fun x ↦ η ‖x - x₀‖) :=
    tsupport_smul_subset_left (fun x ↦ η ‖x - x₀‖) (fun x ↦ x - x₀)
  have h2 : tsupport (fun x ↦ η ‖x - x₀‖) ⊆ (fun x : Space d ↦ ‖x - x₀‖) ⁻¹' tsupport η :=
    tsupport_comp_subset_preimage η (continuous_id.sub continuous_const).norm
  intro x hx
  have hmem : ‖x - x₀‖ ∈ Iio R₀ := hts (h2 (h1 hx))
  simpa [mem_ball, dist_eq_norm] using hmem

theorem hasCompactSupport_radialVectorField {d : ℕ} {η : ℝ → ℝ} (x₀ : Space d) {R₀ : ℝ}
    (hts : tsupport η ⊆ Iio R₀) :
    HasCompactSupport (fun x ↦ η ‖x - x₀‖ • (x - x₀)) :=
  (isCompact_closedBall x₀ R₀).of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_radialVectorField_subset x₀ hts).trans ball_subset_closedBall)

private theorem fderiv_comp_norm_sub_apply {d : ℕ} {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (x₀ : Space d) (hconst : ∃ ε > 0, ∀ s, |s| < ε → η s = η 0) (x v : Space d) :
    fderiv ℝ (fun y ↦ η ‖y - x₀‖) x v = deriv η ‖x - x₀‖ * (inner ℝ (x - x₀) v / ‖x - x₀‖) := by
  obtain ⟨ε, hε, hε_eq⟩ := hconst
  have hderiv0 : deriv η 0 = 0 := by
    refine ((hasDerivAt_const (0 : ℝ) (η 0)).congr_of_eventuallyEq ?_).deriv
    filter_upwards [ball_mem_nhds (0 : ℝ) hε] with s hs
    exact hε_eq s (by simpa [Real.dist_eq] using hs)
  by_cases hx : x = x₀
  · subst hx
    have hf0 : fderiv ℝ (fun y ↦ η ‖y - x‖) x = 0 := by
      refine ((hasFDerivAt_const (η 0) x).congr_of_eventuallyEq ?_).fderiv
      filter_upwards [ball_mem_nhds x hε] with y hy
      exact hε_eq ‖y - x‖ (by
        rw [abs_of_nonneg (norm_nonneg _)]
        simpa [mem_ball, dist_eq_norm] using hy)
    simp [hf0, hderiv0]
  · have hne : ‖x - x₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
    have hsq_ne : ‖x - x₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 hne
    have hsq := ((hasFDerivAt_id x).sub_const x₀).norm_sq
    have hsqrt := hsq.sqrt hsq_ne
    dsimp only [id_eq] at hsqrt
    have hfun_norm : (fun y : Space d ↦ Real.sqrt (‖y - x₀‖ ^ 2)) = fun y ↦ ‖y - x₀‖ := by
      funext y
      exact Real.sqrt_sq (norm_nonneg _)
    rw [hfun_norm, Real.sqrt_sq (norm_nonneg _)] at hsqrt
    have hcomp := (hη.differentiable one_ne_zero ‖x - x₀‖).hasDerivAt.comp_hasFDerivAt x hsqrt
    change HasFDerivAt (fun y ↦ η ‖y - x₀‖) _ x at hcomp
    rw [hcomp.fderiv]
    simp only [smul_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, comp_apply, id_apply,
      innerSL_apply_apply]
    field_simp

/-- Pointwise radial first variation integrand identity (BV10.1) at every point `x` where
`‖ν‖ = 1` (valid for all `m : ℕ` and both `x ≠ x₀` and `x = x₀`). -/
theorem radial_first_variation_integrand_eq {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {η : ℝ → ℝ} (hη : ContDiff ℝ 2 η)
    (x₀ : Space (m + 1)) (hconst : ∃ ε > 0, ∀ s, |s| < ε → η s = η 0)
    (x : Space (m + 1)) {ν : Space (m + 1)} (hν : ‖ν‖ = 1) :
    let X : Space (m + 1) → Space (m + 1) := fun y ↦ η ‖y - x₀‖ • (y - x₀)
    fieldDivergence b X x - inner ℝ ν (fderiv ℝ X x ν) =
      (m : ℝ) * η ‖x - x₀‖ + ‖x - x₀‖ * deriv η ‖x - x₀‖ -
        deriv η ‖x - x₀‖ * (inner ℝ (x - x₀) ν) ^ 2 / ‖x - x₀‖ := by
  intro X
  let φ : Space (m + 1) → ℝ := fun y ↦ η ‖y - x₀‖
  have hφ_diff : DifferentiableAt ℝ φ x :=
    (contDiff_comp_norm_sub hη x₀ hconst).differentiable (by norm_num) x
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  change fieldDivergence b (fun y ↦ φ y • (y - x₀)) x -
    inner ℝ ν (fderiv ℝ (fun y ↦ φ y • (y - x₀)) x ν) = _
  rw [fieldDivergence_smul_sub_const b hφ_diff x₀, fderiv_smul_sub_const hφ_diff x₀ ν,
    inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hν, one_pow, mul_one]
  dsimp only [φ]
  rw [fderiv_comp_norm_sub_apply hη1 x₀ hconst x (x - x₀),
    fderiv_comp_norm_sub_apply hη1 x₀ hconst x ν, real_inner_self_eq_norm_sq,
    real_inner_comm ν (x - x₀)]
  by_cases hx : x = x₀
  · subst hx
    simp [Nat.cast_add, Nat.cast_one]
    ring
  · have hne : ‖x - x₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
    push_cast
    field_simp
    ring

/-- Radial first variation stationarity (BV10.1) on `ball x₀ R₀` for any Radon perimeter
representation `(μ, ν)` of a local perimeter minimizer. -/
theorem radial_first_variation_eq_zero {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {E : Set (Space (m + 1))}
    (hE : MeasurableSet E) {x₀ : Space (m + 1)} {R₀ : ℝ}
    (hmin : ∀ D, MeasurableSet D →
      (∃ K, IsCompact K ∧ K ⊆ ball x₀ R₀ ∧ ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) →
      variationalPerimeter b E (ball x₀ R₀) ≤ variationalPerimeter b D (ball x₀ R₀))
    (μ : Measure (Space (m + 1))) {ν : Space (m + 1) → Space (m + 1)}
    (hν : Integrable ν (μ.restrict (ball x₀ R₀)))
    (hνunit : ∀ᵐ x ∂μ.restrict (ball x₀ R₀), ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport F ⊆ ball x₀ R₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict (ball x₀ R₀))
    {η : ℝ → ℝ} (hη : ContDiff ℝ 2 η) (hts : tsupport η ⊆ Iio R₀)
    (hconst : ∃ ε > 0, ∀ s, |s| < ε → η s = η 0) :
    ∫ x, ((m : ℝ) * η ‖x - x₀‖ + ‖x - x₀‖ * deriv η ‖x - x₀‖ -
      deriv η ‖x - x₀‖ * (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖)
        ∂(μ.restrict (ball x₀ R₀)) = 0 := by
  let X : Space (m + 1) → Space (m + 1) := fun y ↦ η ‖y - x₀‖ • (y - x₀)
  have hfv := perimeter_first_variation_eq_zero_of_contDiff_two b hE isOpen_ball hmin μ hν hνunit
    hdist (contDiff_radialVectorField hη x₀ hconst)
    (hasCompactSupport_radialVectorField x₀ hts) (tsupport_radialVectorField_subset x₀ hts)
  rw [← hfv]
  refine integral_congr_ae ?_
  filter_upwards [hνunit] with x hx
  exact (radial_first_variation_integrand_eq b hη x₀ hconst x hx).symm

/-- `IsLocalPerimeterMinimizer` form of `radial_first_variation_eq_zero` (BV10.1). -/
theorem IsLocalPerimeterMinimizer.radial_first_variation_eq_zero {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} {R₀ : ℝ}
    (hsub : ball x₀ R₀ ⊆ Ω)
    (μ : Measure (Space (m + 1))) {ν : Space (m + 1) → Space (m + 1)}
    (hν : Integrable ν (μ.restrict (ball x₀ R₀)))
    (hνunit : ∀ᵐ x ∂μ.restrict (ball x₀ R₀), ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport F ⊆ ball x₀ R₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict (ball x₀ R₀))
    {η : ℝ → ℝ} (hη : ContDiff ℝ 2 η) (hts : tsupport η ⊆ Iio R₀)
    (hconst : ∃ ε > 0, ∀ s, |s| < ε → η s = η 0) :
    ∫ x, ((m : ℝ) * η ‖x - x₀‖ + ‖x - x₀‖ * deriv η ‖x - x₀‖ -
      deriv η ‖x - x₀‖ * (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖)
        ∂(μ.restrict (ball x₀ R₀)) = 0 :=
  SerrinEpigraph.radial_first_variation_eq_zero b hmin.measurableSet
    (fun D hD ⟨K, hK, hKb, hED⟩ ↦ hmin.minimizes (ball x₀ R₀) D K isOpen_ball hsub hD hK hKb hED)
    μ hν hνunit hdist hη hts hconst

/-! ### 2. Exact Perimeter Monotonicity Formula and Density Monotonicity (BV10.2) -/

private theorem exists_mem_Ioo_of_ae {P : ℝ → Prop} {a b : ℝ} (hab : a < b)
    (hae : ∀ᵐ r : ℝ ∂volume, P r) : ∃ r ∈ Ioo a b, P r := by
  by_contra hnone
  have hsub : Ioo a b ⊆ {r | ¬ P r} := fun r hr hp ↦ hnone ⟨r, hr, hp⟩
  have hzero : volume (Ioo a b) = 0 := measure_mono_null hsub (ae_iff.mp hae)
  rw [Real.volume_Ioo] at hzero
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' hzero

private def monotonicityCutoff (δ s : ℝ) : ℝ :=
  Real.smoothTransition ((1 - s) / δ)

private theorem monotonicityCutoff_contDiff (δ : ℝ) (n : ℕ) :
    ContDiff ℝ n (monotonicityCutoff δ) := by
  unfold monotonicityCutoff
  fun_prop

private theorem monotonicityCutoff_mem_Icc (δ s : ℝ) :
    monotonicityCutoff δ s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem monotonicityCutoff_eq_one {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ 1 - δ) :
    monotonicityCutoff δ s = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr (by linarith))

private theorem monotonicityCutoff_eq_zero {δ s : ℝ} (hδ : 0 < δ) (hs : 1 ≤ s) :
    monotonicityCutoff δ s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)

private theorem monotonicityCutoff_antitone {δ : ℝ} (hδ : 0 < δ) :
    Antitone (monotonicityCutoff δ) := fun _ _ hs ↦
  Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hδ.le)

private theorem deriv_monotonicityCutoff_nonpos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    deriv (monotonicityCutoff δ) s ≤ 0 := by
  have hmono : Monotone (fun u ↦ -monotonicityCutoff δ u) := fun u₁ u₂ hu ↦
    neg_le_neg (monotonicityCutoff_antitone hδ hu)
  have hnonneg : 0 ≤ deriv (fun u ↦ -monotonicityCutoff δ u) s :=
    monotone_deriv_nonneg_everywhere hmono s
  have hneg : deriv (fun u ↦ -monotonicityCutoff δ u) s = -deriv (monotonicityCutoff δ) s := by
    change deriv (-monotonicityCutoff δ) s = _
    exact deriv.neg
  linarith

private theorem deriv_monotonicityCutoff_eq_zero_of_le {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ 1 - δ) :
    deriv (monotonicityCutoff δ) s = 0 := by
  have hlow (u : ℝ) (hu : u < 1 - δ) : deriv (monotonicityCutoff δ) u = 0 := by
    refine ((hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq ?_).deriv
    filter_upwards [Iio_mem_nhds hu] with v hv
    exact monotonicityCutoff_eq_one hδ hv.le
  rcases hs.lt_or_eq with hlt | rfl
  · exact hlow s hlt
  · have hcont : Continuous (deriv (monotonicityCutoff δ)) :=
      (monotonicityCutoff_contDiff δ 1).continuous_deriv_one
    have hseq : Tendsto (fun k : ℕ ↦ 1 - δ - 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 - δ)) := by
      simpa only [sub_zero] using
        tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim := (hcont.tendsto (1 - δ)).comp hseq
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun k ↦
      (hlow _ (by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity])).symm)

private theorem deriv_monotonicityCutoff_eq_zero_of_ge {δ s : ℝ} (hδ : 0 < δ) (hs : 1 ≤ s) :
    deriv (monotonicityCutoff δ) s = 0 := by
  have hhigh (u : ℝ) (hu : 1 < u) : deriv (monotonicityCutoff δ) u = 0 := by
    refine ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq ?_).deriv
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact monotonicityCutoff_eq_zero hδ hv.le
  rcases hs.lt_or_eq with hlt | rfl
  · exact hhigh _ hlt
  · have hcont : Continuous (deriv (monotonicityCutoff δ)) :=
      (monotonicityCutoff_contDiff δ 1).continuous_deriv_one
    have hseq : Tendsto (fun k : ℕ ↦ (1 : ℝ) + 1 / ((k : ℝ) + 1)) atTop (𝓝 1) := by
      simpa only [add_zero] using
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim := (hcont.tendsto 1).comp hseq
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun k ↦
      (hhigh _ (by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity])).symm)

private theorem hasCompactSupport_deriv_monotonicityCutoff {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (deriv (monotonicityCutoff δ)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 1 - δ) (b := 1)) ?_
  intro s hs
  constructor
  · by_contra hlt
    exact hs (deriv_monotonicityCutoff_eq_zero_of_le hδ (le_of_not_ge hlt))
  · by_contra hgt
    exact hs (deriv_monotonicityCutoff_eq_zero_of_ge hδ (le_of_not_ge hgt))

private def monotonicityKernel (m : ℕ) (δ s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..s, u ^ m * deriv (monotonicityCutoff δ) u

private theorem hasDerivAt_monotonicityKernel (m : ℕ) (δ s : ℝ) :
    HasDerivAt (monotonicityKernel m δ) (s ^ m * deriv (monotonicityCutoff δ) s) s := by
  have hc : Continuous (fun u : ℝ ↦ u ^ m * deriv (monotonicityCutoff δ) u) :=
    (continuous_pow m).mul (monotonicityCutoff_contDiff δ 1).continuous_deriv_one
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    (hc.stronglyMeasurableAtFilter volume (𝓝 s)) hc.continuousAt

private theorem continuous_monotonicityKernel (m : ℕ) (δ : ℝ) :
    Continuous (monotonicityKernel m δ) :=
  Differentiable.continuous fun s ↦ (hasDerivAt_monotonicityKernel m δ s).differentiableAt

private theorem monotonicityKernel_eq_zero_of_le (m : ℕ) {δ s : ℝ}
    (hδ : 0 < δ) (hs0 : 0 ≤ s) (hs : s ≤ 1 - δ) :
    monotonicityKernel m δ s = 0 := by
  unfold monotonicityKernel
  rw [intervalIntegral.integral_of_le hs0]
  refine setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦ ?_
  rw [deriv_monotonicityCutoff_eq_zero_of_le hδ (hu.2.trans hs), mul_zero]

private theorem monotonicityKernel_eq_one_of_ge (m : ℕ) {δ s : ℝ}
    (hδ : 0 < δ) (hs : 1 ≤ s) :
    monotonicityKernel m δ s = monotonicityKernel m δ 1 := by
  have hc : Continuous (fun u : ℝ ↦ u ^ m * deriv (monotonicityCutoff δ) u) :=
    (continuous_pow m).mul (monotonicityCutoff_contDiff δ 1).continuous_deriv_one
  unfold monotonicityKernel
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 1)
    (hc.intervalIntegrable 1 s)]
  have htail : (∫ u in (1 : ℝ)..s, u ^ m * deriv (monotonicityCutoff δ) u) = 0 := by
    rw [intervalIntegral.integral_of_le hs]
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦ ?_
    rw [deriv_monotonicityCutoff_eq_zero_of_ge hδ hu.1.le, mul_zero]
  rw [htail, add_zero]

private theorem monotonicityKernel_one_bounds (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    -1 ≤ monotonicityKernel m δ 1 ∧ monotonicityKernel m δ 1 ≤ -(1 - δ) ^ m := by
  have hc : Continuous (fun u : ℝ ↦ u ^ m * deriv (monotonicityCutoff δ) u) :=
    (continuous_pow m).mul (monotonicityCutoff_contDiff δ 1).continuous_deriv_one
  have hc_d : Continuous (deriv (monotonicityCutoff δ)) :=
    (monotonicityCutoff_contDiff δ 1).continuous_deriv_one
  have h1δ_pos : 0 ≤ 1 - δ := by linarith
  have h1δ_le : 1 - δ ≤ 1 := by linarith
  have hsplit : monotonicityKernel m δ 1 =
      ∫ u in (1 - δ)..1, u ^ m * deriv (monotonicityCutoff δ) u := by
    have h0 := monotonicityKernel_eq_zero_of_le m hδ h1δ_pos le_rfl
    unfold monotonicityKernel at h0 ⊢
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1 - δ))
      (hc.intervalIntegrable (1 - δ) 1), h0, zero_add]
  have hint_deriv : (∫ u in (1 - δ)..1, deriv (monotonicityCutoff δ) u) = -1 := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun u _ ↦ (monotonicityCutoff_contDiff δ 1).differentiable one_ne_zero u)
      (hc_d.intervalIntegrable (1 - δ) 1),
      monotonicityCutoff_eq_zero hδ le_rfl, monotonicityCutoff_eq_one hδ le_rfl, zero_sub]
  rw [hsplit]
  constructor
  · calc
      -1 = ∫ u in (1 - δ)..1, deriv (monotonicityCutoff δ) u := hint_deriv.symm
      _ ≤ ∫ u in (1 - δ)..1, u ^ m * deriv (monotonicityCutoff δ) u := by
          refine intervalIntegral.integral_mono_on h1δ_le
            (hc_d.intervalIntegrable (1 - δ) 1) (hc.intervalIntegrable (1 - δ) 1) fun u hu ↦ ?_
          have hu_pow : u ^ m ≤ 1 := pow_le_one₀ (h1δ_pos.trans hu.1) hu.2
          have hd_np : deriv (monotonicityCutoff δ) u ≤ 0 := deriv_monotonicityCutoff_nonpos hδ u
          nlinarith
  · calc
      (∫ u in (1 - δ)..1, u ^ m * deriv (monotonicityCutoff δ) u)
        ≤ ∫ u in (1 - δ)..1, (1 - δ) ^ m * deriv (monotonicityCutoff δ) u := by
          refine intervalIntegral.integral_mono_on h1δ_le
            (hc.intervalIntegrable (1 - δ) 1)
            ((hc_d.const_mul _).intervalIntegrable (1 - δ) 1) fun u hu ↦ ?_
          have hu_pow : (1 - δ) ^ m ≤ u ^ m := pow_le_pow_left₀ h1δ_pos hu.1 m
          have hd_np : deriv (monotonicityCutoff δ) u ≤ 0 := deriv_monotonicityCutoff_nonpos hδ u
          exact mul_le_mul_of_nonpos_right hu_pow hd_np
      _ = (1 - δ) ^ m * ∫ u in (1 - δ)..1, deriv (monotonicityCutoff δ) u :=
          intervalIntegral.integral_const_mul _ _
      _ = -(1 - δ) ^ m := by rw [hint_deriv]; ring

private theorem monotonicityKernel_diff_bounds (m : ℕ) {δ s₁ s₂ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hs₁ : 0 ≤ s₁) (hs₁₂ : s₁ ≤ s₂) :
    0 ≤ monotonicityKernel m δ s₁ - monotonicityKernel m δ s₂ ∧
      monotonicityKernel m δ s₁ - monotonicityKernel m δ s₂ ≤ 1 := by
  have hc : Continuous (fun u : ℝ ↦ u ^ m * deriv (monotonicityCutoff δ) u) :=
    (continuous_pow m).mul (monotonicityCutoff_contDiff δ 1).continuous_deriv_one
  have hanti (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      monotonicityKernel m δ b ≤ monotonicityKernel m δ a := by
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 a) (hc.intervalIntegrable (μ := volume) a b)
    change monotonicityKernel m δ a + (∫ u in a..b, u ^ m * deriv (monotonicityCutoff δ) u) =
      monotonicityKernel m δ b at hadj
    have htail_np : (∫ u in a..b, u ^ m * deriv (monotonicityCutoff δ) u) ≤ 0 := by
      rw [intervalIntegral.integral_of_le hab]
      refine setIntegral_nonpos measurableSet_Ioc fun u hu ↦ ?_
      exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (ha.trans hu.1.le) m)
        (deriv_monotonicityCutoff_nonpos hδ u)
    linarith
  have h0 : monotonicityKernel m δ 0 = 0 := by simp [monotonicityKernel]
  have hs₁_le0 : monotonicityKernel m δ s₁ ≤ 0 := h0 ▸ hanti 0 s₁ le_rfl hs₁
  have hs₂_ge1 : monotonicityKernel m δ 1 ≤ monotonicityKernel m δ s₂ := by
    rcases le_or_gt s₂ 1 with hs₂1 | hs₂1
    · exact hanti s₂ 1 (hs₁.trans hs₁₂) hs₂1
    · rw [monotonicityKernel_eq_one_of_ge m hδ hs₂1.le]
  have h1_low := (monotonicityKernel_one_bounds m hδ hδ1).1
  have hle_diff := hanti s₁ s₂ hs₁ hs₁₂
  constructor <;> linarith

private theorem smoothed_perimeter_monotonicity_identity {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {E : Set (Space (m + 1))}
    (hE : MeasurableSet E) {x₀ : Space (m + 1)} {r R R₀ δ : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRR₀ : R < R₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hmin : ∀ D, MeasurableSet D →
      (∃ K, IsCompact K ∧ K ⊆ ball x₀ R₀ ∧ ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) →
      variationalPerimeter b E (ball x₀ R₀) ≤ variationalPerimeter b D (ball x₀ R₀))
    (μ : Measure (Space (m + 1))) {ν : Space (m + 1) → Space (m + 1)}
    (hν : Integrable ν (μ.restrict (ball x₀ R₀)))
    (hνunit : ∀ᵐ x ∂μ.restrict (ball x₀ R₀), ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport F ⊆ ball x₀ R₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict (ball x₀ R₀)) :
    let μ₀ := μ.restrict (ball x₀ R₀)
    R ^ (-(m : ℤ)) * (∫ x, monotonicityCutoff δ (‖x - x₀‖ / R) ∂μ₀) -
      r ^ (-(m : ℤ)) * (∫ x, monotonicityCutoff δ (‖x - x₀‖ / r) ∂μ₀) =
      ∫ x, ((inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2)) *
        (monotonicityKernel m δ (‖x - x₀‖ / R) - monotonicityKernel m δ (‖x - x₀‖ / r)) ∂μ₀ := by
  intro μ₀
  have hμ₀_fin : IsFiniteMeasure μ₀ := by
    constructor
    have heq : (∫⁻ _, (1 : ℝ≥0∞) ∂μ₀) = ∫⁻ x, ‖ν x‖ₑ ∂μ₀ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hνunit] with x hx
      simp [← ofReal_norm, hx]
    rw [lintegral_const, one_mul] at heq
    exact heq ▸ hν.2
  let ν₀ : Space (m + 1) → Space (m + 1) := hν.aestronglyMeasurable.mk ν
  have hν₀_meas : Measurable ν₀ := hν.aestronglyMeasurable.measurable_mk
  let ν₁ : Space (m + 1) → Space (m + 1) := fun x ↦ if ‖ν₀ x‖ = 1 then ν₀ x else 0
  have hν₁_meas : Measurable ν₁ :=
    Measurable.ite (measurableSet_eq_fun hν₀_meas.norm measurable_const) hν₀_meas measurable_const
  have hν₁_le (x : Space (m + 1)) : ‖ν₁ x‖ ≤ 1 := by
    dsimp [ν₁]
    split_ifs with h
    · exact h.le
    · simp
  have hν₁_ae : ν₁ =ᵐ[μ₀] ν := by
    filter_upwards [hν.aestronglyMeasurable.ae_eq_mk, hνunit] with x hx_mk hx_u
    have hx_eq : ν₀ x = ν x := hx_mk.symm
    have hn : ‖ν₀ x‖ = 1 := by rw [hx_eq, hx_u]
    simp only [ν₁, hx_eq, hx_u, ↓reduceIte]
  let φ : ℝ → ℝ := monotonicityCutoff δ
  have hφ_cd2 : ContDiff ℝ 2 φ := monotonicityCutoff_contDiff δ 2
  have hφ_cd1 : ContDiff ℝ 1 φ := monotonicityCutoff_contDiff δ 1
  have hφ'_cont : Continuous (deriv φ) := hφ_cd1.continuous_deriv_one
  obtain ⟨B₀, hB₀⟩ := (hasCompactSupport_deriv_monotonicityCutoff hδ).exists_bound_of_continuous
    hφ'_cont
  let B : ℝ := max B₀ 0
  have hB_nonneg : 0 ≤ B := le_max_right B₀ 0
  have hφ'_le (u : ℝ) : ‖deriv φ u‖ ≤ B := (hB₀ u).trans (le_max_left B₀ 0)
  let I_fn : ℝ → ℝ := fun t ↦ ∫ x, φ (‖x - x₀‖ / t) ∂μ₀
  let Θ : ℝ → ℝ := fun t ↦ t ^ (-(m : ℤ)) * I_fn t
  let K_fn : ℝ → Space (m + 1) → ℝ := fun t x ↦
    -(t ^ (m + 2))⁻¹ * deriv φ (‖x - x₀‖ / t) * (inner ℝ (x - x₀) (ν₁ x)) ^ 2 / ‖x - x₀‖
  have hcs_div_le (x : Space (m + 1)) : (inner ℝ (x - x₀) (ν₁ x)) ^ 2 / ‖x - x₀‖ ≤ ‖x - x₀‖ := by
    by_cases hx : x = x₀
    · simp [hx]
    · have hρ : 0 < ‖x - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
      have hcs : |inner ℝ (x - x₀) (ν₁ x)| ≤ ‖x - x₀‖ := by
        calc
          |inner ℝ (x - x₀) (ν₁ x)| ≤ ‖x - x₀‖ * ‖ν₁ x‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖x - x₀‖ * 1 := mul_le_mul_of_nonneg_left (hν₁_le x) hρ.le
          _ = ‖x - x₀‖ := mul_one _
      have hsq : (inner ℝ (x - x₀) (ν₁ x)) ^ 2 ≤ ‖x - x₀‖ ^ 2 := by
        simpa only [sq_abs] using sq_le_sq.mpr (by rwa [abs_of_pos hρ])
      rw [div_le_iff₀ hρ, ← sq]
      exact hsq
  have hcs_div_nonneg (x : Space (m + 1)) : 0 ≤ (inner ℝ (x - x₀) (ν₁ x)) ^ 2 / ‖x - x₀‖ :=
    div_nonneg (sq_nonneg _) (norm_nonneg _)
  have hΘ_deriv (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < R₀) :
      HasDerivAt Θ (∫ x, K_fn t x ∂μ₀) t := by
    let a : ℝ := t / 2
    let b_up : ℝ := (t + R₀) / 2
    have ha_pos : 0 < a := half_pos ht_pos
    have hat : a < t := half_lt_self ht_pos
    have htb : t < b_up := by dsimp [b_up]; linarith
    have hc_φ (s : ℝ) : Continuous (fun x : Space (m + 1) ↦ φ (‖x - x₀‖ / s)) :=
      hφ_cd1.continuous.comp (((continuous_id.sub continuous_const).norm).div_const s)
    have hc_φ' : Continuous
        (fun x : Space (m + 1) ↦ deriv φ (‖x - x₀‖ / t) * (-‖x - x₀‖ / t ^ 2)) :=
      (hφ'_cont.comp (((continuous_id.sub continuous_const).norm).div_const t)).mul
        ((((continuous_id.sub continuous_const).norm).neg).div_const (t ^ 2))
    have hI_deriv : HasDerivAt I_fn
        (∫ x, deriv φ (‖x - x₀‖ / t) * (-‖x - x₀‖ / t ^ 2) ∂μ₀) t := by
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ₀)
        (s := Ioo a b_up) (bound := fun _ ↦ B * (b_up / a ^ 2))
        (F := fun s x ↦ φ (‖x - x₀‖ / s))
        (F' := fun s x ↦ deriv φ (‖x - x₀‖ / s) * (-‖x - x₀‖ / s ^ 2))
        (Ioo_mem_nhds hat htb)
        (Eventually.of_forall fun s ↦ (hc_φ s).aestronglyMeasurable)
        (Integrable.of_bound (hc_φ t).aestronglyMeasurable 1
          (Eventually.of_forall fun x ↦ by
            have hv := monotonicityCutoff_mem_Icc δ (‖x - x₀‖ / t)
            rw [Real.norm_of_nonneg hv.1]
            exact hv.2))
        hc_φ'.aestronglyMeasurable
        ?_ (integrable_const _) ?_).2
      · refine Eventually.of_forall fun x s hs ↦ ?_
        have hs_pos : 0 < s := ha_pos.trans hs.1
        by_cases h1 : 1 < ‖x - x₀‖ / s
        · rw [deriv_monotonicityCutoff_eq_zero_of_ge hδ h1.le, zero_mul, norm_zero]
          exact mul_nonneg hB_nonneg (div_nonneg (ht_pos.trans htb).le (sq_nonneg a))
        · have h1_le : ‖x - x₀‖ / s ≤ 1 := le_of_not_gt h1
          have hnorm_le : ‖x - x₀‖ ≤ b_up := ((div_le_one hs_pos).mp h1_le).trans hs.2.le
          have hquot_le : ‖-‖x - x₀‖ / s ^ 2‖ ≤ b_up / a ^ 2 := by
            rw [neg_div, norm_neg, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (sq_nonneg s))]
            exact div_le_div₀ (ht_pos.trans htb).le hnorm_le (sq_pos_of_pos ha_pos)
              (pow_le_pow_left₀ ha_pos.le hs.1.le 2)
          rw [norm_mul]
          exact mul_le_mul (hφ'_le _) hquot_le (norm_nonneg _) hB_nonneg
      · refine Eventually.of_forall fun x s hs ↦ ?_
        have hs_pos : 0 < s := ha_pos.trans hs.1
        have hdiv : HasDerivAt (fun u : ℝ ↦ ‖x - x₀‖ / u) (-‖x - x₀‖ / s ^ 2) s := by
          convert (hasDerivAt_const s ‖x - x₀‖).div (hasDerivAt_id s) hs_pos.ne' using 1
          · rfl
          · simp only [id_eq]
            ring
        exact (hφ_cd1.differentiable one_ne_zero (‖x - x₀‖ / s)).hasDerivAt.comp s hdiv
    have hprod := (hasDerivAt_zpow (-(m : ℤ)) t (Or.inl ht_pos.ne')).mul hI_deriv
    let η : ℝ → ℝ := fun u ↦ φ (u / t)
    have hη_cd2 : ContDiff ℝ 2 η := hφ_cd2.comp (contDiff_id.div_const t)
    have hη_ts : tsupport η ⊆ Iio R₀ := by
      refine (closure_minimal ?_ isClosed_Iic).trans (Iic_subset_Iio.mpr ht_lt)
      intro u hu
      by_contra hgt
      exact hu (monotonicityCutoff_eq_zero hδ ((one_le_div ht_pos).mpr (le_of_not_ge hgt)))
    have hη_const : ∃ ε > 0, ∀ u, |u| < ε → η u = η 0 := by
      refine ⟨(1 - δ) * t, mul_pos (by linarith) ht_pos, fun u hu ↦ ?_⟩
      have hu_lt : u < (1 - δ) * t := lt_of_le_of_lt (le_abs_self u) hu
      have hquot : u / t ≤ 1 - δ := ((div_lt_iff₀ ht_pos).mpr hu_lt).le
      dsimp [η, φ]
      rw [monotonicityCutoff_eq_one hδ hquot,
        monotonicityCutoff_eq_one hδ (by rw [zero_div]; linarith)]
    have hη_deriv (u : ℝ) : deriv η u = deriv φ (u / t) * t⁻¹ := by
      have hd := (hφ_cd1.differentiable one_ne_zero (u / t)).hasDerivAt.comp u
        ((hasDerivAt_id u).div_const t)
      change deriv (φ ∘ fun v ↦ v / t) u = _
      simpa only [id_eq, one_div] using hd.deriv
    have hfv := radial_first_variation_eq_zero b hE hmin μ hν hνunit hdist hη_cd2 hη_ts hη_const
    simp_rw [hη_deriv] at hfv
    have hfv₁ : ∫ x, ((m : ℝ) * φ (‖x - x₀‖ / t) +
        ‖x - x₀‖ * (deriv φ (‖x - x₀‖ / t) * t⁻¹) -
        deriv φ (‖x - x₀‖ / t) * t⁻¹ * (inner ℝ (x - x₀) (ν₁ x)) ^ 2 / ‖x - x₀‖) ∂μ₀ = 0 := by
      rw [← hfv]
      refine integral_congr_ae ?_
      filter_upwards [hν₁_ae] with x hx
      dsimp only [η]
      rw [hx]
    have hi_term1 : Integrable (fun x ↦ (m : ℝ) * φ (‖x - x₀‖ / t)) μ₀ :=
      Integrable.of_bound (continuous_const.mul (hc_φ t)).aestronglyMeasurable ((m : ℝ) * 1)
        (Eventually.of_forall fun x ↦ by
          have hv := monotonicityCutoff_mem_Icc δ (‖x - x₀‖ / t)
          rw [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg m), Real.norm_of_nonneg hv.1]
          exact mul_le_mul_of_nonneg_left hv.2 (Nat.cast_nonneg m))
    have hc_term2 : Continuous
        (fun x : Space (m + 1) ↦ ‖x - x₀‖ * (deriv φ (‖x - x₀‖ / t) * t⁻¹)) :=
      ((continuous_id.sub continuous_const).norm).mul
        ((hφ'_cont.comp (((continuous_id.sub continuous_const).norm).div_const t)).mul
          continuous_const)
    have hi_term2 : Integrable (fun x ↦ ‖x - x₀‖ * (deriv φ (‖x - x₀‖ / t) * t⁻¹)) μ₀ :=
      Integrable.of_bound hc_term2.aestronglyMeasurable (t * (B * t⁻¹))
        (Eventually.of_forall fun x ↦ by
          by_cases h1 : 1 < ‖x - x₀‖ / t
          · rw [deriv_monotonicityCutoff_eq_zero_of_ge hδ h1.le, zero_mul, mul_zero, norm_zero]
            exact mul_nonneg ht_pos.le (mul_nonneg hB_nonneg (inv_nonneg.mpr ht_pos.le))
          · have hle_t : ‖x - x₀‖ ≤ t := (div_le_one ht_pos).mp (le_of_not_gt h1)
            rw [norm_mul, norm_mul, norm_norm, Real.norm_of_nonneg (inv_nonneg.mpr ht_pos.le)]
            exact mul_le_mul hle_t
              (mul_le_mul_of_nonneg_right (hφ'_le _) (inv_nonneg.mpr ht_pos.le))
              (by positivity) ht_pos.le)
    have hi_term3 : Integrable
        (fun x ↦ deriv φ (‖x - x₀‖ / t) * t⁻¹ * (inner ℝ (x - x₀) (ν₁ x)) ^ 2 / ‖x - x₀‖) μ₀ := by
      have hm : Measurable
          (fun x ↦ deriv φ (‖x - x₀‖ / t) * t⁻¹ * (inner ℝ (x - x₀) (ν₁ x)) ^ 2 / ‖x - x₀‖) :=
        (((hφ'_cont.measurable.comp ((measurable_id.sub measurable_const).norm.div_const t)).mul
          measurable_const).mul
          (((measurable_id.sub measurable_const).inner hν₁_meas).pow_const 2)).div
          (measurable_id.sub measurable_const).norm
      refine Integrable.of_bound hm.aestronglyMeasurable (B * t⁻¹ * t)
        (Eventually.of_forall fun x ↦ ?_)
      by_cases h1 : 1 < ‖x - x₀‖ / t
      · rw [deriv_monotonicityCutoff_eq_zero_of_ge hδ h1.le, zero_mul, zero_mul, zero_div,
          norm_zero]
        exact mul_nonneg (mul_nonneg hB_nonneg (inv_nonneg.mpr ht_pos.le)) ht_pos.le
      · have hle_t : ‖x - x₀‖ ≤ t := (div_le_one ht_pos).mp (le_of_not_gt h1)
        rw [mul_div_assoc, norm_mul, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr ht_pos.le),
          Real.norm_of_nonneg (hcs_div_nonneg x)]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (hφ'_le _) (inv_nonneg.mpr ht_pos.le))
          ((hcs_div_le x).trans hle_t) (hcs_div_nonneg x)
          (mul_nonneg hB_nonneg (inv_nonneg.mpr ht_pos.le))
    have hfv_split := integral_sub (hi_term1.add hi_term2) hi_term3
    simp only [Pi.add_apply] at hfv_split
    rw [hfv_split, integral_add hi_term1 hi_term2, integral_const_mul] at hfv₁
    have hi_scale : (∫ x, deriv φ (‖x - x₀‖ / t) * (-‖x - x₀‖ / t ^ 2) ∂μ₀) =
        -t⁻¹ * ∫ x, ‖x - x₀‖ * (deriv φ (‖x - x₀‖ / t) * t⁻¹) ∂μ₀ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      field_simp
    have hK_scale : (∫ x, K_fn t x ∂μ₀) =
        -(t ^ (m + 1))⁻¹ *
          ∫ x, deriv φ (‖x - x₀‖ / t) * t⁻¹ * (inner ℝ (x - x₀) (ν₁ x)) ^ 2 / ‖x - x₀‖ ∂μ₀ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      dsimp only [K_fn]
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      field_simp
    refine hprod.congr_deriv ?_
    dsimp only [I_fn]
    have hz1 : t ^ (-(m : ℤ) - 1) = (t ^ (m + 1))⁻¹ := by
      rw [show -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    have hz0 : t ^ (-(m : ℤ)) = (t ^ m)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hz1, hz0, hi_scale, hK_scale]
    have hrel : (∫ x, deriv φ (‖x - x₀‖ / t) * t⁻¹ *
        (inner ℝ (x - x₀) (ν₁ x)) ^ 2 / ‖x - x₀‖ ∂μ₀) =
        (m : ℝ) * (∫ x, φ (‖x - x₀‖ / t) ∂μ₀) +
          ∫ x, ‖x - x₀‖ * (deriv φ (‖x - x₀‖ / t) * t⁻¹) ∂μ₀ := by
      linarith [hfv₁]
    rw [hrel, pow_succ]
    push_cast
    field_simp
    ring
  let μT : Measure ℝ := volume.restrict (Icc r R)
  have hμT_fin : IsFiniteMeasure μT := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hK_meas : Measurable (Function.uncurry K_fn) := by
    have hnorm_m : Measurable (fun p : ℝ × Space (m + 1) ↦ ‖p.2 - x₀‖) :=
      (measurable_snd.sub measurable_const).norm
    exact ((((((measurable_fst.pow_const (m + 2)).inv).neg).mul
      (hφ'_cont.measurable.comp (hnorm_m.div measurable_fst))).mul
      (((measurable_snd.sub measurable_const).inner (hν₁_meas.comp measurable_snd)).pow_const 2))
        |>.div hnorm_m)
  have hK_prod_int : Integrable (Function.uncurry K_fn) (μT.prod μ₀) := by
    refine Integrable.of_bound hK_meas.aestronglyMeasurable ((r ^ (m + 2))⁻¹ * B * R) ?_
    have hae_Icc : ∀ᵐ p : ℝ × Space (m + 1) ∂(μT.prod μ₀), p.1 ∈ Icc r R :=
      (Measure.quasiMeasurePreserving_fst (μ := μT) (ν := μ₀)).ae
        (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hae_Icc] with p hp
    have ht_pos : 0 < p.1 := hr.trans_le hp.1
    change ‖K_fn p.1 p.2‖ ≤ _
    dsimp only [K_fn]
    by_cases h1 : 1 < ‖p.2 - x₀‖ / p.1
    · rw [deriv_monotonicityCutoff_eq_zero_of_ge hδ h1.le]
      simp only [mul_zero, zero_mul, zero_div, norm_zero]
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)) hB_nonneg)
        (hr.trans hrR).le
    · have hle_R : ‖p.2 - x₀‖ ≤ R := ((div_le_one ht_pos).mp (le_of_not_gt h1)).trans hp.2
      have ht_pow_le : (p.1 ^ (m + 2))⁻¹ ≤ (r ^ (m + 2))⁻¹ :=
        inv_anti₀ (pow_pos hr _) (pow_le_pow_left₀ hr.le hp.1 (m + 2))
      rw [mul_div_assoc, norm_mul, norm_mul, norm_neg,
        Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg ht_pos.le _)),
        Real.norm_of_nonneg (hcs_div_nonneg p.2)]
      exact mul_le_mul
        (mul_le_mul ht_pow_le (hφ'_le _) (norm_nonneg _)
          (inv_nonneg.mpr (pow_nonneg hr.le _)))
        ((hcs_div_le p.2).trans hle_R) (hcs_div_nonneg p.2)
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)) hB_nonneg)
  have hΘ'_int : IntervalIntegrable (fun t ↦ ∫ x, K_fn t x ∂μ₀) volume r R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hrR.le).mpr hK_prod_int.integral_prod_left
  have hftc : (∫ t in r..R, ∫ x, K_fn t x ∂μ₀) = Θ R - Θ r :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ by
        rw [uIcc_of_le hrR.le] at ht
        exact hΘ_deriv t (hr.trans_le ht.1) (ht.2.trans_lt hRR₀))
      hΘ'_int
  have hswap : (∫ t in r..R, ∫ x, K_fn t x ∂μ₀) = ∫ x, (∫ t in r..R, K_fn t x) ∂μ₀ := by
    rw [intervalIntegral.integral_of_le hrR.le, ← integral_Icc_eq_integral_Ioc]
    change (∫ t, (∫ x, K_fn t x ∂μ₀) ∂μT) = _
    rw [integral_integral_swap hK_prod_int]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    change (∫ t in Icc r R, K_fn t x) = ∫ t in r..R, K_fn t x
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrR.le]
  have hinner_eval (x : Space (m + 1)) :
      (∫ t in r..R, K_fn t x) =
        ((inner ℝ (x - x₀) (ν₁ x)) ^ 2 / ‖x - x₀‖ ^ (m + 2)) *
          (monotonicityKernel m δ (‖x - x₀‖ / R) - monotonicityKernel m δ (‖x - x₀‖ / r)) := by
    let ρ : ℝ := ‖x - x₀‖
    by_cases hx : x = x₀
    · subst hx
      simp [K_fn]
    · have hρ : 0 < ρ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
      let c_x : ℝ := (inner ℝ (x - x₀) (ν₁ x)) ^ 2 / ρ ^ (m + 2)
      have hprim : ∀ t ∈ uIcc r R,
          HasDerivAt (fun s ↦ c_x * monotonicityKernel m δ (ρ / s)) (K_fn t x) t := by
        intro t ht
        rw [uIcc_of_le hrR.le] at ht
        have ht_pos : 0 < t := hr.trans_le ht.1
        have hdiv : HasDerivAt (fun s : ℝ ↦ ρ / s) (-ρ / t ^ 2) t := by
          convert (hasDerivAt_const t ρ).div (hasDerivAt_id t) ht_pos.ne' using 1
          · rfl
          · simp only [id_eq]
            ring
        have hk := ((hasDerivAt_monotonicityKernel m δ (ρ / t)).comp t hdiv).const_mul c_x
        refine hk.congr_deriv ?_
        have hρ_ne : ‖x - x₀‖ ≠ 0 := hρ.ne'
        have ht_ne : t ≠ 0 := ht_pos.ne'
        dsimp only [c_x, K_fn, ρ, φ]
        rw [div_pow, show m + 2 = m + 1 + 1 by omega, pow_succ ‖x - x₀‖, pow_succ ‖x - x₀‖,
          pow_succ t, pow_succ t]
        field_simp
        ring
      have hK_cont : ContinuousOn (fun t ↦ K_fn t x) (uIcc r R) := by
        rw [uIcc_of_le hrR.le]
        intro t ht
        have ht_ne : t ≠ 0 := (hr.trans_le ht.1).ne'
        exact ((((((continuousAt_id.pow (m + 2)).inv₀ (pow_ne_zero _ ht_ne)).neg).mul
          (hφ'_cont.continuousAt.comp (continuousAt_const.div continuousAt_id ht_ne))).mul
          continuousAt_const).div_const _).continuousWithinAt
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim (hK_cont.intervalIntegrable),
        ← mul_sub]
  rw [← hftc, hswap]
  refine integral_congr_ae ?_
  filter_upwards [hν₁_ae] with x hx
  rw [hinner_eval x, hx]

private theorem sphere_free_perimeter_monotonicity_identity {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {E : Set (Space (m + 1))}
    (hE : MeasurableSet E) {x₀ : Space (m + 1)} {r R R₀ : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRR₀ : R < R₀)
    (hmin : ∀ D, MeasurableSet D →
      (∃ K, IsCompact K ∧ K ⊆ ball x₀ R₀ ∧ ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) →
      variationalPerimeter b E (ball x₀ R₀) ≤ variationalPerimeter b D (ball x₀ R₀))
    (μ : Measure (Space (m + 1))) {ν : Space (m + 1) → Space (m + 1)}
    (hν : Integrable ν (μ.restrict (ball x₀ R₀)))
    (hνunit : ∀ᵐ x ∂μ.restrict (ball x₀ R₀), ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport F ⊆ ball x₀ R₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict (ball x₀ R₀))
    (hsph_r : (μ.restrict (ball x₀ R₀)) (sphere x₀ r) = 0)
    (hsph_R : (μ.restrict (ball x₀ R₀)) (sphere x₀ R) = 0) :
    let μ₀ := μ.restrict (ball x₀ R₀)
    R ^ (-(m : ℤ)) * μ₀.real (ball x₀ R) - r ^ (-(m : ℤ)) * μ₀.real (ball x₀ r) =
      ∫ x in ball x₀ R \ closedBall x₀ r,
        (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2) ∂μ₀ := by
  intro μ₀
  have hμ₀_fin : IsFiniteMeasure μ₀ := by
    constructor
    have heq : (∫⁻ _, (1 : ℝ≥0∞) ∂μ₀) = ∫⁻ x, ‖ν x‖ₑ ∂μ₀ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hνunit] with x hx
      simp [← ofReal_norm, hx]
    rw [lintegral_const, one_mul] at heq
    exact heq ▸ hν.2
  let δ : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 3)
  have hδ_pos (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hδ_half (k : ℕ) : δ k ≤ 1 / 2 := by
    dsimp [δ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hδ_lim : Tendsto δ atTop (𝓝 0) := by
    have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
    refine h0.congr fun k ↦ ?_
    dsimp [δ, Function.comp_def]
    push_cast
    ring_nf
  have hball_lim {t : ℝ} (ht : 0 < t) (hsph : μ₀ (sphere x₀ t) = 0) :
      Tendsto (fun k ↦ ∫ x, monotonicityCutoff (δ k) (‖x - x₀‖ / t) ∂μ₀) atTop
        (𝓝 (μ₀.real (ball x₀ t))) := by
    have hgoal : μ₀.real (ball x₀ t) = ∫ x, (ball x₀ t).indicator (fun _ ↦ (1 : ℝ)) x ∂μ₀ := by
      rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one]
    rw [hgoal]
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (fun k ↦ ((monotonicityCutoff_contDiff (δ k) 1).continuous.comp
        (((continuous_id.sub continuous_const).norm).div_const t)).aestronglyMeasurable)
      (integrable_const _)
      (fun k ↦ Eventually.of_forall fun x ↦ by
        have hv := monotonicityCutoff_mem_Icc (δ k) (‖x - x₀‖ / t)
        rw [Real.norm_of_nonneg hv.1]
        exact hv.2)
      ?_
    filter_upwards [compl_mem_ae_iff.mpr hsph] with x hx_not_sph
    by_cases hxb : x ∈ ball x₀ t
    · rw [indicator_of_mem hxb]
      have hlt : ‖x - x₀‖ / t < 1 :=
        (div_lt_one ht).mpr (by simpa [mem_ball, dist_eq_norm] using hxb)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hδ_lim.eventually (gt_mem_nhds (sub_pos.mpr hlt))] with k hk
      exact (monotonicityCutoff_eq_one (hδ_pos k) (by linarith)).symm
    · rw [indicator_of_notMem hxb]
      have hne : dist x x₀ ≠ t := fun hh ↦ hx_not_sph (mem_sphere.mpr hh)
      have hgt : t < ‖x - x₀‖ := by
        have hge : t ≤ dist x x₀ := le_of_not_gt (by simpa [mem_ball] using hxb)
        simpa [dist_eq_norm] using lt_of_le_of_ne hge hne.symm
      have h1 : 1 ≤ ‖x - x₀‖ / t := (one_le_div ht).mpr hgt.le
      exact tendsto_const_nhds.congr fun k ↦
        (monotonicityCutoff_eq_zero (hδ_pos k) h1).symm
  let A : Set (Space (m + 1)) := ball x₀ R \ closedBall x₀ r
  have hA_meas : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  let f_seq : ℕ → Space (m + 1) → ℝ := fun k x ↦
    ((inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2)) *
      (monotonicityKernel m (δ k) (‖x - x₀‖ / R) - monotonicityKernel m (δ k) (‖x - x₀‖ / r))
  let f_lim : Space (m + 1) → ℝ :=
    A.indicator (fun x ↦ (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2))
  have hrhs_lim : Tendsto (fun k ↦ ∫ x, f_seq k x ∂μ₀) atTop (𝓝 (∫ x, f_lim x ∂μ₀)) := by
    have hg_meas : AEStronglyMeasurable
        (fun x ↦ (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2)) μ₀ := by
      simp_rw [div_eq_mul_inv]
      exact ((((continuous_id.sub continuous_const).aestronglyMeasurable.inner
        hν.aestronglyMeasurable).pow 2).mul
          ((((measurable_id.sub measurable_const).norm.pow_const (m + 2)).inv).aestronglyMeasurable))
    have hk_diff_cont (k : ℕ) : Continuous (fun x : Space (m + 1) ↦
        monotonicityKernel m (δ k) (‖x - x₀‖ / R) - monotonicityKernel m (δ k) (‖x - x₀‖ / r)) :=
      ((continuous_monotonicityKernel m (δ k)).comp
        (((continuous_id.sub continuous_const).norm).div_const R)).sub
        ((continuous_monotonicityKernel m (δ k)).comp
          (((continuous_id.sub continuous_const).norm).div_const r))
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ ((r / 2) ^ m)⁻¹)
      (fun k ↦ hg_meas.mul (hk_diff_cont k).aestronglyMeasurable)
      (integrable_const _)
      (fun k ↦ ?_) ?_
    · filter_upwards [hνunit] with x hx_u
      dsimp only [f_seq]
      have hs₁ : 0 ≤ ‖x - x₀‖ / R := div_nonneg (norm_nonneg _) (hr.trans hrR).le
      have hs₁₂ : ‖x - x₀‖ / R ≤ ‖x - x₀‖ / r :=
        div_le_div_of_nonneg_left (norm_nonneg _) hr hrR.le
      have hdiff_b := monotonicityKernel_diff_bounds m (hδ_pos k) (hδ_half k) hs₁ hs₁₂
      by_cases hlow : ‖x - x₀‖ ≤ r / 2
      · have hq_r : ‖x - x₀‖ / r ≤ 1 - δ k := by
          have h1 : ‖x - x₀‖ / r ≤ 1 / 2 := (div_le_div_iff₀ hr (by norm_num)).mpr (by linarith)
          linarith [hδ_half k]
        rw [monotonicityKernel_eq_zero_of_le m (hδ_pos k) hs₁ (hs₁₂.trans hq_r),
          monotonicityKernel_eq_zero_of_le m (hδ_pos k) (hs₁.trans hs₁₂) hq_r,
          sub_self, mul_zero, norm_zero]
        positivity
      · have hlow_gt : r / 2 < ‖x - x₀‖ := lt_of_not_ge hlow
        have hρ_pos : 0 < ‖x - x₀‖ := (half_pos hr).trans hlow_gt
        have hcs : (inner ℝ (x - x₀) (ν x)) ^ 2 ≤ ‖x - x₀‖ ^ 2 := by
          have habs : |inner ℝ (x - x₀) (ν x)| ≤ ‖x - x₀‖ := by
            calc
              |inner ℝ (x - x₀) (ν x)| ≤ ‖x - x₀‖ * ‖ν x‖ := abs_real_inner_le_norm _ _
              _ = ‖x - x₀‖ := by rw [hx_u, mul_one]
          simpa only [sq_abs] using sq_le_sq.mpr (by rwa [abs_of_pos hρ_pos])
        have hquot_le : (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2) ≤ ((r / 2) ^ m)⁻¹ := by
          have hp : ‖x - x₀‖ ^ (m + 2) = ‖x - x₀‖ ^ m * ‖x - x₀‖ ^ 2 := by
            rw [← pow_add]
          rw [hp, div_mul_eq_div_div, div_le_iff₀ (sq_pos_of_pos hρ_pos)]
          calc
            (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ m
              ≤ ‖x - x₀‖ ^ 2 / ‖x - x₀‖ ^ m :=
                div_le_div_of_nonneg_right hcs (pow_nonneg hρ_pos.le m)
            _ = (‖x - x₀‖ ^ m)⁻¹ * ‖x - x₀‖ ^ 2 := by ring
            _ ≤ ((r / 2) ^ m)⁻¹ * ‖x - x₀‖ ^ 2 :=
                mul_le_mul_of_nonneg_right
                  (inv_anti₀ (pow_pos (half_pos hr) m)
                    (pow_le_pow_left₀ (half_pos hr).le hlow_gt.le m))
                  (sq_nonneg _)
        rw [norm_mul, Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg hρ_pos.le _)),
          Real.norm_of_nonneg hdiff_b.1]
        calc
          ((inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2)) *
              (monotonicityKernel m (δ k) (‖x - x₀‖ / R) -
                monotonicityKernel m (δ k) (‖x - x₀‖ / r))
            ≤ ((r / 2) ^ m)⁻¹ * 1 :=
              mul_le_mul hquot_le hdiff_b.2 hdiff_b.1 (by positivity)
          _ = ((r / 2) ^ m)⁻¹ := mul_one _
    · have h1_lim : Tendsto (fun k ↦ monotonicityKernel m (δ k) 1) atTop (𝓝 (-1)) := by
        have hup : Tendsto (fun k ↦ -(1 - δ k) ^ m) atTop (𝓝 (-1)) := by
          simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub hδ_lim).pow m).neg
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
          (fun k ↦ (monotonicityKernel_one_bounds m (hδ_pos k) (hδ_half k)).1)
          (fun k ↦ (monotonicityKernel_one_bounds m (hδ_pos k) (hδ_half k)).2)
      filter_upwards [compl_mem_ae_iff.mpr hsph_r, compl_mem_ae_iff.mpr hsph_R] with x hnr hnR
      have hne_r : ‖x - x₀‖ ≠ r := fun hh ↦ hnr (by simpa [mem_sphere, dist_eq_norm] using hh)
      have hne_R : ‖x - x₀‖ ≠ R := fun hh ↦ hnR (by simpa [mem_sphere, dist_eq_norm] using hh)
      rcases lt_or_gt_of_ne hne_r with hlt_r | hgt_r
      · have hxnotA : x ∉ A := fun hxA ↦
          hxA.2 (by simpa [mem_closedBall, dist_eq_norm] using hlt_r.le)
        dsimp only [f_seq, f_lim]
        rw [indicator_of_notMem hxnotA]
        have hq_r : ‖x - x₀‖ / r < 1 := (div_lt_one hr).mpr hlt_r
        have hq_R : ‖x - x₀‖ / R ≤ ‖x - x₀‖ / r :=
          div_le_div_of_nonneg_left (norm_nonneg _) hr hrR.le
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hδ_lim.eventually (gt_mem_nhds (sub_pos.mpr hq_r))] with k hk
        have hle1 : ‖x - x₀‖ / r ≤ 1 - δ k := by linarith
        rw [monotonicityKernel_eq_zero_of_le m (hδ_pos k)
          (div_nonneg (norm_nonneg _) (hr.trans hrR).le) (hq_R.trans hle1),
          monotonicityKernel_eq_zero_of_le m (hδ_pos k) (div_nonneg (norm_nonneg _) hr.le) hle1,
          sub_self, mul_zero]
      · rcases lt_or_gt_of_ne hne_R with hlt_R | hgt_R
        · have hxA : x ∈ A := ⟨by simpa [mem_ball, dist_eq_norm] using hlt_R,
            by simpa [mem_closedBall, dist_eq_norm, not_le] using hgt_r⟩
          dsimp only [f_seq, f_lim]
          rw [indicator_of_mem hxA]
          have hq_R : ‖x - x₀‖ / R < 1 := (div_lt_one (hr.trans hrR)).mpr hlt_R
          have hq_r : 1 ≤ ‖x - x₀‖ / r := (one_le_div hr).mpr hgt_r.le
          have hker_R : Tendsto (fun k ↦ monotonicityKernel m (δ k) (‖x - x₀‖ / R)) atTop (𝓝 0) := by
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [hδ_lim.eventually (gt_mem_nhds (sub_pos.mpr hq_R))] with k hk
            exact (monotonicityKernel_eq_zero_of_le m (hδ_pos k)
              (div_nonneg (norm_nonneg _) (hr.trans hrR).le) (by linarith)).symm
          have hker_r : Tendsto (fun k ↦ monotonicityKernel m (δ k) (‖x - x₀‖ / r))
              atTop (𝓝 (-1)) :=
            h1_lim.congr fun k ↦ (monotonicityKernel_eq_one_of_ge m (hδ_pos k) hq_r).symm
          simpa only [zero_sub, neg_neg, mul_one] using
            tendsto_const_nhds.mul (hker_R.sub hker_r)
        · have hxnotA : x ∉ A := fun hxA ↦
            not_lt_of_ge hgt_R.le (by simpa [mem_ball, dist_eq_norm] using hxA.1)
          dsimp only [f_seq, f_lim]
          rw [indicator_of_notMem hxnotA]
          have hq_R : 1 ≤ ‖x - x₀‖ / R := (one_le_div (hr.trans hrR)).mpr hgt_R.le
          have hq_r : 1 ≤ ‖x - x₀‖ / r := (one_le_div hr).mpr (hrR.trans hgt_R).le
          refine tendsto_const_nhds.congr fun k ↦ ?_
          rw [monotonicityKernel_eq_one_of_ge m (hδ_pos k) hq_R,
            monotonicityKernel_eq_one_of_ge m (hδ_pos k) hq_r, sub_self, mul_zero]
  have hlhs_lim : Tendsto
      (fun k ↦ R ^ (-(m : ℤ)) * (∫ x, monotonicityCutoff (δ k) (‖x - x₀‖ / R) ∂μ₀) -
        r ^ (-(m : ℤ)) * (∫ x, monotonicityCutoff (δ k) (‖x - x₀‖ / r) ∂μ₀))
      atTop (𝓝 (R ^ (-(m : ℤ)) * μ₀.real (ball x₀ R) - r ^ (-(m : ℤ)) * μ₀.real (ball x₀ r))) :=
    (tendsto_const_nhds.mul (hball_lim (hr.trans hrR) hsph_R)).sub
      (tendsto_const_nhds.mul (hball_lim hr hsph_r))
  have heq_seq (k : ℕ) :
      R ^ (-(m : ℤ)) * (∫ x, monotonicityCutoff (δ k) (‖x - x₀‖ / R) ∂μ₀) -
        r ^ (-(m : ℤ)) * (∫ x, monotonicityCutoff (δ k) (‖x - x₀‖ / r) ∂μ₀) =
        ∫ x, f_seq k x ∂μ₀ :=
    smoothed_perimeter_monotonicity_identity b hE hr hrR hRR₀ (hδ_pos k) (hδ_half k)
      hmin μ hν hνunit hdist
  have hlim_eq := tendsto_nhds_unique hlhs_lim (hrhs_lim.congr fun k ↦ (heq_seq k).symm)
  rwa [integral_indicator hA_meas] at hlim_eq

/-- Unconditional exact perimeter monotonicity formula with `closedBall` inner term (BV10.2):
valid for EVERY `0 < r < R < R₀` without any sphere-atom assumption. -/
theorem perimeter_monotonicity_closedBall_identity {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {E : Set (Space (m + 1))}
    (hE : MeasurableSet E) {x₀ : Space (m + 1)} {r R R₀ : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRR₀ : R < R₀)
    (hmin : ∀ D, MeasurableSet D →
      (∃ K, IsCompact K ∧ K ⊆ ball x₀ R₀ ∧ ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) →
      variationalPerimeter b E (ball x₀ R₀) ≤ variationalPerimeter b D (ball x₀ R₀))
    (μ : Measure (Space (m + 1))) {ν : Space (m + 1) → Space (m + 1)}
    (hν : Integrable ν (μ.restrict (ball x₀ R₀)))
    (hνunit : ∀ᵐ x ∂μ.restrict (ball x₀ R₀), ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport F ⊆ ball x₀ R₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict (ball x₀ R₀)) :
    R ^ (-(m : ℤ)) * μ.real (ball x₀ R) - r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r) =
      ∫ x in ball x₀ R \ closedBall x₀ r,
        (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2) ∂μ := by
  let μ₀ := μ.restrict (ball x₀ R₀)
  have hμ₀_fin : IsFiniteMeasure μ₀ := by
    constructor
    have heq : (∫⁻ _, (1 : ℝ≥0∞) ∂μ₀) = ∫⁻ x, ‖ν x‖ₑ ∂μ₀ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hνunit] with x hx
      simp [← ofReal_norm, hx]
    rw [lintegral_const, one_mul] at heq
    exact heq ▸ hν.2
  let mid : ℝ := (r + R) / 2
  have hr_mid : r < mid := by dsimp [mid]; linarith
  have hmid_R : mid < R := by dsimp [mid]; linarith
  have hae_sph : ∀ᵐ s : ℝ ∂volume, 0 < s → μ₀ (sphere x₀ s) = 0 :=
    ae_sphere_measure_eq_zero μ₀ x₀
  have hex_r (j : ℕ) :
      ∃ s ∈ Ioo r (min mid (r + 1 / ((j : ℝ) + 1))), μ₀ (sphere x₀ s) = 0 := by
    have hub : r < min mid (r + 1 / ((j : ℝ) + 1)) :=
      lt_min hr_mid (lt_add_of_pos_right r (by positivity))
    obtain ⟨s, hs, h0⟩ := exists_mem_Ioo_of_ae hub hae_sph
    exact ⟨s, hs, h0 (hr.trans hs.1)⟩
  choose r_seq hr_seq_mem hr_seq_sph using hex_r
  have hr_seq_lim : Tendsto r_seq atTop (𝓝 r) := by
    have hup : Tendsto (fun j : ℕ ↦ r + 1 / ((j : ℝ) + 1)) atTop (𝓝 r) := by
      simpa only [add_zero] using
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun j ↦ (hr_seq_mem j).1.le)
      (fun j ↦ (hr_seq_mem j).2.le.trans (min_le_right _ _))
  have hex_R (j : ℕ) :
      ∃ s ∈ Ioo (max mid (R - 1 / ((j : ℝ) + 1))) R, μ₀ (sphere x₀ s) = 0 := by
    have hlb : max mid (R - 1 / ((j : ℝ) + 1)) < R :=
      max_lt hmid_R (by linarith [show (0 : ℝ) < 1 / ((j : ℝ) + 1) by positivity])
    have hlb_pos : 0 < max mid (R - 1 / ((j : ℝ) + 1)) :=
      (hr.trans hr_mid).trans_le (le_max_left _ _)
    obtain ⟨s, hs, h0⟩ := exists_mem_Ioo_of_ae hlb hae_sph
    exact ⟨s, hs, h0 (hlb_pos.trans hs.1)⟩
  choose R_seq hR_seq_mem hR_seq_sph using hex_R
  have hR_seq_lim : Tendsto R_seq atTop (𝓝 R) := by
    have hlo : Tendsto (fun j : ℕ ↦ R - 1 / ((j : ℝ) + 1)) atTop (𝓝 R) := by
      simpa only [sub_zero] using
        tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
      (fun j ↦ (le_max_right _ _).trans (hR_seq_mem j).1.le)
      (fun j ↦ (hR_seq_mem j).2.le)
  have hμ_R_lim : Tendsto (fun j ↦ μ₀.real (ball x₀ (R_seq j))) atTop (𝓝 (μ₀.real (ball x₀ R))) := by
    have heq_j (j : ℕ) : μ₀.real (ball x₀ (R_seq j)) =
        ∫ x, (ball x₀ (R_seq j)).indicator (fun _ ↦ (1 : ℝ)) x ∂μ₀ := by
      rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one]
    have heq_R : μ₀.real (ball x₀ R) = ∫ x, (ball x₀ R).indicator (fun _ ↦ (1 : ℝ)) x ∂μ₀ := by
      rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one]
    simp_rw [heq_j, heq_R]
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (fun j ↦ (measurable_const.indicator measurableSet_ball).aestronglyMeasurable)
      (integrable_const _)
      (fun j ↦ Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ ball x₀ (R_seq j) <;> simp [hx])
      (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ ball x₀ R
    · rw [indicator_of_mem hx]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hR_seq_lim.eventually (lt_mem_nhds (mem_ball.mp hx))] with j hj
      exact (indicator_of_mem (mem_ball.mpr hj) (fun _ ↦ (1 : ℝ))).symm
    · rw [indicator_of_notMem hx]
      refine tendsto_const_nhds.congr fun j ↦ ?_
      have hxnot : x ∉ ball x₀ (R_seq j) :=
        fun hh ↦ hx (ball_subset_ball (hR_seq_mem j).2.le hh)
      exact (indicator_of_notMem hxnot (fun _ ↦ (1 : ℝ))).symm
  have hμ_r_lim :
      Tendsto (fun j ↦ μ₀.real (ball x₀ (r_seq j))) atTop (𝓝 (μ₀.real (closedBall x₀ r))) := by
    have heq_j (j : ℕ) : μ₀.real (ball x₀ (r_seq j)) =
        ∫ x, (ball x₀ (r_seq j)).indicator (fun _ ↦ (1 : ℝ)) x ∂μ₀ := by
      rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one]
    have heq_r : μ₀.real (closedBall x₀ r) =
        ∫ x, (closedBall x₀ r).indicator (fun _ ↦ (1 : ℝ)) x ∂μ₀ := by
      rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul, mul_one]
    simp_rw [heq_j, heq_r]
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (fun j ↦ (measurable_const.indicator measurableSet_ball).aestronglyMeasurable)
      (integrable_const _)
      (fun j ↦ Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ ball x₀ (r_seq j) <;> simp [hx])
      (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ closedBall x₀ r
    · rw [indicator_of_mem hx]
      refine tendsto_const_nhds.congr fun j ↦ ?_
      have hxb : x ∈ ball x₀ (r_seq j) :=
        closedBall_subset_ball (hr_seq_mem j).1 hx
      exact (indicator_of_mem hxb (fun _ ↦ (1 : ℝ))).symm
    · rw [indicator_of_notMem hx]
      have hgt : r < dist x x₀ := lt_of_not_ge (by simpa [mem_closedBall] using hx)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hr_seq_lim.eventually (gt_mem_nhds hgt)] with j hj
      have hxnot : x ∉ ball x₀ (r_seq j) := by simpa [mem_ball, not_lt] using hj.le
      exact (indicator_of_notMem hxnot (fun _ ↦ (1 : ℝ))).symm
  let g : Space (m + 1) → ℝ := fun x ↦ (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2)
  have hg_meas : AEStronglyMeasurable g μ₀ := by
    dsimp only [g]
    simp_rw [div_eq_mul_inv]
    exact ((((continuous_id.sub continuous_const).aestronglyMeasurable.inner
      hν.aestronglyMeasurable).pow 2).mul
        ((((measurable_id.sub measurable_const).norm.pow_const (m + 2)).inv).aestronglyMeasurable))
  let A_j : ℕ → Set (Space (m + 1)) := fun j ↦ ball x₀ (R_seq j) \ closedBall x₀ (r_seq j)
  let A : Set (Space (m + 1)) := ball x₀ R \ closedBall x₀ r
  have hA_j_meas (j : ℕ) : MeasurableSet (A_j j) := measurableSet_ball.diff measurableSet_closedBall
  have hA_meas : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hrhs_lim :
      Tendsto (fun j ↦ ∫ x in A_j j, g x ∂μ₀) atTop (𝓝 (∫ x in A, g x ∂μ₀)) := by
    simp_rw [← integral_indicator (hA_j_meas _), ← integral_indicator hA_meas]
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (r ^ m)⁻¹)
      (fun j ↦ hg_meas.indicator (hA_j_meas j))
      (integrable_const _)
      (fun j ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · filter_upwards [hνunit] with x hx_u
      by_cases hxA : x ∈ A_j j
      · rw [indicator_of_mem hxA]
        have hr_lt : r < ‖x - x₀‖ :=
          (hr_seq_mem j).1.trans (lt_of_not_ge (by simpa [mem_closedBall, dist_eq_norm] using hxA.2))
        have hρ_pos : 0 < ‖x - x₀‖ := hr.trans hr_lt
        have hcs : (inner ℝ (x - x₀) (ν x)) ^ 2 ≤ ‖x - x₀‖ ^ 2 := by
          have habs : |inner ℝ (x - x₀) (ν x)| ≤ ‖x - x₀‖ := by
            calc
              |inner ℝ (x - x₀) (ν x)| ≤ ‖x - x₀‖ * ‖ν x‖ := abs_real_inner_le_norm _ _
              _ = ‖x - x₀‖ := by rw [hx_u, mul_one]
          simpa only [sq_abs] using sq_le_sq.mpr (by rwa [abs_of_pos hρ_pos])
        dsimp only [g]
        rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg hρ_pos.le _))]
        have hp : ‖x - x₀‖ ^ (m + 2) = ‖x - x₀‖ ^ m * ‖x - x₀‖ ^ 2 := by rw [← pow_add]
        rw [hp, div_mul_eq_div_div, div_le_iff₀ (sq_pos_of_pos hρ_pos)]
        calc
          (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ m
            ≤ ‖x - x₀‖ ^ 2 / ‖x - x₀‖ ^ m :=
              div_le_div_of_nonneg_right hcs (pow_nonneg hρ_pos.le m)
          _ = (‖x - x₀‖ ^ m)⁻¹ * ‖x - x₀‖ ^ 2 := by ring
          _ ≤ (r ^ m)⁻¹ * ‖x - x₀‖ ^ 2 :=
              mul_le_mul_of_nonneg_right
                (inv_anti₀ (pow_pos hr m) (pow_le_pow_left₀ hr.le hr_lt.le m)) (sq_nonneg _)
      · rw [indicator_of_notMem hxA, norm_zero]
        positivity
    · by_cases hxA : x ∈ A
      · rw [indicator_of_mem hxA]
        have hlt_R : dist x x₀ < R := mem_ball.mp hxA.1
        have hgt_r : r < dist x x₀ := lt_of_not_ge (by simpa [mem_closedBall] using hxA.2)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hR_seq_lim.eventually (lt_mem_nhds hlt_R),
          hr_seq_lim.eventually (gt_mem_nhds hgt_r)] with j hjR hjr
        have hxAj : x ∈ A_j j := ⟨mem_ball.mpr hjR, by simpa [mem_closedBall, not_le] using hjr⟩
        exact (indicator_of_mem hxAj g).symm
      · rw [indicator_of_notMem hxA]
        refine tendsto_const_nhds.congr fun j ↦ ?_
        have hxnot : x ∉ A_j j := by
          rintro ⟨h1, h2⟩
          exact hxA ⟨ball_subset_ball (hR_seq_mem j).2.le h1,
            fun hc ↦ h2 (closedBall_subset_closedBall (hr_seq_mem j).1.le hc)⟩
        exact (indicator_of_notMem hxnot g).symm
  have hlhs_lim : Tendsto
      (fun j ↦ (R_seq j) ^ (-(m : ℤ)) * μ₀.real (ball x₀ (R_seq j)) -
        (r_seq j) ^ (-(m : ℤ)) * μ₀.real (ball x₀ (r_seq j)))
      atTop (𝓝 (R ^ (-(m : ℤ)) * μ₀.real (ball x₀ R) -
        r ^ (-(m : ℤ)) * μ₀.real (closedBall x₀ r))) :=
    (((hR_seq_lim.zpow₀ _ (Or.inl (hr.trans hrR).ne')).mul hμ_R_lim).sub
      ((hr_seq_lim.zpow₀ _ (Or.inl hr.ne')).mul hμ_r_lim))
  have heq_j (j : ℕ) :
      (R_seq j) ^ (-(m : ℤ)) * μ₀.real (ball x₀ (R_seq j)) -
        (r_seq j) ^ (-(m : ℤ)) * μ₀.real (ball x₀ (r_seq j)) =
        ∫ x in A_j j, g x ∂μ₀ := by
    have hr_j_pos : 0 < r_seq j := hr.trans (hr_seq_mem j).1
    have hrR_j : r_seq j < R_seq j :=
      ((hr_seq_mem j).2.trans_le (min_le_left _ _)).trans
        ((le_max_left _ _).trans_lt (hR_seq_mem j).1)
    have hRR₀_j : R_seq j < R₀ := (hR_seq_mem j).2.trans hRR₀
    exact sphere_free_perimeter_monotonicity_identity b hE hr_j_pos hrR_j hRR₀_j
      hmin μ hν hνunit hdist (hr_seq_sph j) (hR_seq_sph j)
  have hμ₀_id := tendsto_nhds_unique hlhs_lim (hrhs_lim.congr fun j ↦ (heq_j j).symm)
  have hR_sub : ball x₀ R ⊆ ball x₀ R₀ := ball_subset_ball hRR₀.le
  have hr_sub : closedBall x₀ r ⊆ ball x₀ R₀ := closedBall_subset_ball (hrR.trans hRR₀)
  have hA_sub : A ⊆ ball x₀ R₀ := sdiff_subset.trans hR_sub
  have hμ_R : μ₀.real (ball x₀ R) = μ.real (ball x₀ R) := by
    simp [μ₀, Measure.real, Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hR_sub]
  have hμ_r : μ₀.real (closedBall x₀ r) = μ.real (closedBall x₀ r) := by
    simp [μ₀, Measure.real, Measure.restrict_apply measurableSet_closedBall,
      inter_eq_left.mpr hr_sub]
  have hμ_A : μ₀.restrict A = μ.restrict A := by
    rw [Measure.restrict_restrict hA_meas, inter_eq_left.mpr hA_sub]
  rwa [hμ_R, hμ_r, hμ_A] at hμ₀_id

/-- `IsLocalPerimeterMinimizer` form of the exact `closedBall` monotonicity identity (BV10.2). -/
theorem IsLocalPerimeterMinimizer.perimeter_monotonicity_closedBall_identity {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} {r R R₀ : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRR₀ : R < R₀) (hsub : ball x₀ R₀ ⊆ Ω)
    (μ : Measure (Space (m + 1))) {ν : Space (m + 1) → Space (m + 1)}
    (hν : Integrable ν (μ.restrict (ball x₀ R₀)))
    (hνunit : ∀ᵐ x ∂μ.restrict (ball x₀ R₀), ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport F ⊆ ball x₀ R₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict (ball x₀ R₀)) :
    R ^ (-(m : ℤ)) * μ.real (ball x₀ R) - r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r) =
      ∫ x in ball x₀ R \ closedBall x₀ r,
        (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2) ∂μ :=
  SerrinEpigraph.perimeter_monotonicity_closedBall_identity b hmin.measurableSet
    hr hrR hRR₀
    (fun D hD ⟨K, hK, hKb, hED⟩ ↦ hmin.minimizes (ball x₀ R₀) D K isOpen_ball hsub hD hK hKb hED)
    μ hν hνunit hdist

/-- Unconditional open-ball perimeter monotonicity formula (BV10.2) retaining the explicit inner
sphere atom `r ^ (-m) * μ.real (sphere x₀ r)`. -/
theorem IsLocalPerimeterMinimizer.perimeter_monotonicity_ball_sphere_identity {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} {r R R₀ : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRR₀ : R < R₀) (hsub : ball x₀ R₀ ⊆ Ω)
    (μ : Measure (Space (m + 1))) {ν : Space (m + 1) → Space (m + 1)}
    (hν : Integrable ν (μ.restrict (ball x₀ R₀)))
    (hνunit : ∀ᵐ x ∂μ.restrict (ball x₀ R₀), ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport F ⊆ ball x₀ R₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict (ball x₀ R₀)) :
    R ^ (-(m : ℤ)) * μ.real (ball x₀ R) - r ^ (-(m : ℤ)) * μ.real (ball x₀ r) =
      r ^ (-(m : ℤ)) * μ.real (sphere x₀ r) +
        ∫ x in ball x₀ R \ closedBall x₀ r,
          (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2) ∂μ := by
  have hcb_id := hmin.perimeter_monotonicity_closedBall_identity hr hrR hRR₀ hsub μ hν hνunit hdist
  have hμR₀_lt : μ (ball x₀ R₀) < ⊤ := by
    have heq : (∫⁻ _, (1 : ℝ≥0∞) ∂(μ.restrict (ball x₀ R₀))) =
        ∫⁻ x, ‖ν x‖ₑ ∂(μ.restrict (ball x₀ R₀)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hνunit] with x hx
      simp [← ofReal_norm, hx]
    rw [lintegral_const, one_mul, Measure.restrict_apply_univ] at heq
    exact heq ▸ hν.2
  have hunion : closedBall x₀ r = ball x₀ r ∪ sphere x₀ r := by
    ext x
    simp only [mem_closedBall, mem_union, mem_ball, mem_sphere]
    exact le_iff_lt_or_eq
  have hdisj : Disjoint (ball x₀ r) (sphere x₀ r) :=
    disjoint_left.mpr fun x hxb hxs ↦ (mem_ball.mp hxb).ne (mem_sphere.mp hxs)
  have hr_sub : closedBall x₀ r ⊆ ball x₀ R₀ := closedBall_subset_ball (hrR.trans hRR₀)
  have hball_fin : μ (ball x₀ r) ≠ ⊤ :=
    ((measure_mono (ball_subset_closedBall.trans hr_sub)).trans_lt hμR₀_lt).ne
  have hsph_fin : μ (sphere x₀ r) ≠ ⊤ :=
    ((measure_mono (sphere_subset_closedBall.trans hr_sub)).trans_lt hμR₀_lt).ne
  have hcb_real : μ.real (closedBall x₀ r) = μ.real (ball x₀ r) + μ.real (sphere x₀ r) := by
    simp only [Measure.real]
    rw [hunion, measure_union hdisj isClosed_sphere.measurableSet,
      ENNReal.toReal_add hball_fin hsph_fin]
  rw [hcb_real] at hcb_id
  linarith

/-- Open-ball perimeter monotonicity formula (BV10.2) when `μ (sphere x₀ r) = 0`. -/
theorem IsLocalPerimeterMinimizer.perimeter_monotonicity_ball_identity_of_sphere_zero {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} {r R R₀ : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRR₀ : R < R₀) (hsub : ball x₀ R₀ ⊆ Ω)
    (μ : Measure (Space (m + 1))) {ν : Space (m + 1) → Space (m + 1)}
    (hν : Integrable ν (μ.restrict (ball x₀ R₀)))
    (hνunit : ∀ᵐ x ∂μ.restrict (ball x₀ R₀), ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport F ⊆ ball x₀ R₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict (ball x₀ R₀))
    (hsph : μ (sphere x₀ r) = 0) :
    R ^ (-(m : ℤ)) * μ.real (ball x₀ R) - r ^ (-(m : ℤ)) * μ.real (ball x₀ r) =
      ∫ x in ball x₀ R \ closedBall x₀ r,
        (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2) ∂μ := by
  have hid := hmin.perimeter_monotonicity_ball_sphere_identity hr hrR hRR₀ hsub μ hν hνunit hdist
  have hsph_real : μ.real (sphere x₀ r) = 0 := by simp [Measure.real, hsph]
  rw [hsph_real, mul_zero, zero_add] at hid
  exact hid

/-- Monotonicity of `r ↦ r ^ (-m) * P(E, ball x₀ r)` for all `0 < r ≤ R` with
`closedBall x₀ R ⊆ Ω` (valid for all `m : ℕ`). -/
theorem IsLocalPerimeterMinimizer.perimeter_ratio_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hsub : closedBall x₀ R ⊆ Ω) :
    r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal ≤
      R ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ R)).toReal := by
  rcases hrR.eq_or_lt with rfl | hlt
  · exact le_rfl
  · obtain ⟨δ, μ, ν, hδ, hcb, hfin, hzero, hμ_open, hν_int, hν_unit, hdist⟩ :=
      hmin.exists_ball_radon_measure (hr.trans hlt) hsub
    let _ : IsFiniteMeasure μ := hfin
    let R₀ : ℝ := R + δ
    have hRR₀ : R < R₀ := by dsimp [R₀]; linarith
    have hres_self : μ.restrict (ball x₀ R₀) = μ :=
      Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hzero)
    have hid := hmin.perimeter_monotonicity_ball_sphere_identity hr hlt hRR₀
      (ball_subset_closedBall.trans hcb) μ
      (by rwa [hres_self]) (by rwa [hres_self])
      (fun F hF hs ↦ by rw [hres_self]; exact hdist F hF hs)
    have hμ_r : μ.real (ball x₀ r) = (variationalPerimeter b E (ball x₀ r)).toReal := by
      simp [Measure.real, hμ_open (ball x₀ r) isOpen_ball (ball_subset_ball (hlt.trans hRR₀).le)]
    have hμ_R : μ.real (ball x₀ R) = (variationalPerimeter b E (ball x₀ R)).toReal := by
      simp [Measure.real, hμ_open (ball x₀ R) isOpen_ball (ball_subset_ball hRR₀.le)]
    have hs_nn : 0 ≤ r ^ (-(m : ℤ)) * μ.real (sphere x₀ r) :=
      mul_nonneg (zpow_nonneg hr.le _) measureReal_nonneg
    have hint_nn : 0 ≤ ∫ x in ball x₀ R \ closedBall x₀ r,
        (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2) ∂μ :=
      integral_nonneg fun x ↦ div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
    rw [hμ_r, hμ_R] at hid
    linarith

/-- `MonotoneOn` packaging of `IsLocalPerimeterMinimizer.perimeter_ratio_le`. -/
theorem IsLocalPerimeterMinimizer.monotoneOn_perimeter_ratio {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (x₀ : Space (m + 1)) :
    MonotoneOn (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
      {r | 0 < r ∧ closedBall x₀ r ⊆ Ω} :=
  fun _ hr _ hR hrR ↦ hmin.perimeter_ratio_le hr.1 hrR hR.2

/-- Global `MonotoneOn` on `Ioi 0` when `Ω = univ`. -/
theorem IsLocalPerimeterMinimizer.monotoneOn_perimeter_ratio_univ {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) (x₀ : Space (m + 1)) :
    MonotoneOn (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
      (Ioi 0) :=
  fun _ hr _ _ hrR ↦ hmin.perimeter_ratio_le hr hrR (subset_univ _)

/-- In ambient dimension `m + 1 ≥ 2` (`0 < m`), perimeter measures of local perimeter minimizers
have no point atoms inside `Ω`. -/
theorem IsLocalPerimeterMinimizer.measure_singleton_eq_zero {m : ℕ} (hm : 0 < m)
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (μ : Measure (Space (m + 1)))
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U)
    {x₀ : Space (m + 1)} (hx₀ : x₀ ∈ Ω) :
    μ {x₀} = 0 := by
  obtain ⟨r₀, hr₀, hcb₀⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hmin.isOpen_domain.mem_nhds hx₀)
  let r_seq : ℕ → ℝ := fun k ↦ r₀ * (1 / ((k : ℝ) + 1))
  have hbound (k : ℕ) :
      μ {x₀} ≤ ENNReal.ofReal (minimizerPerimeterUpperConst m * (r_seq k) ^ m) := by
    have hrk_pos : 0 < r_seq k := by dsimp [r_seq]; positivity
    have hrk_le : r_seq k ≤ r₀ := by
      dsimp [r_seq]
      have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      nlinarith
    have hcb_k : closedBall x₀ (r_seq k) ⊆ Ω := (closedBall_subset_closedBall hrk_le).trans hcb₀
    calc
      μ {x₀} ≤ μ (ball x₀ (r_seq k)) := measure_mono (singleton_subset_iff.mpr (mem_ball_self hrk_pos))
      _ = variationalPerimeter b E (ball x₀ (r_seq k)) :=
          hμ _ isOpen_ball (ball_subset_closedBall.trans hcb_k)
      _ ≤ ENNReal.ofReal (minimizerPerimeterUpperConst m * (r_seq k) ^ m) :=
          hmin.variationalPerimeter_ball_le hrk_pos hcb_k
  have hr_lim : Tendsto r_seq atTop (𝓝 0) := by
    simpa only [r_seq, mul_zero] using
      tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hrhs_lim : Tendsto
      (fun k ↦ ENNReal.ofReal (minimizerPerimeterUpperConst m * (r_seq k) ^ m)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun k ↦ minimizerPerimeterUpperConst m * (r_seq k) ^ m) atTop (𝓝 0) := by
      simpa only [zero_pow hm.ne', mul_zero] using tendsto_const_nhds.mul (hr_lim.pow m)
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
  exact nonpos_iff_eq_zero.mp (le_of_tendsto_of_tendsto' tendsto_const_nhds hrhs_lim hbound)

/-- Asymptotic perimeter density at `x₀` as `r → 0+`:
`lim_{r → 0+} r ^ (-m) * (variationalPerimeter b E (ball x₀ r)).toReal`. -/
def perimeterDensity {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (E : Set (Space (m + 1))) (x₀ : Space (m + 1)) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ))
    (fun r ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)

/-- At every `x₀ ∈ Ω`, the perimeter ratio `r ^ (-m) * P(E, ball x₀ r)` converges as `r → 0+` to
`perimeterDensity b E x₀`, with `0 ≤ perimeterDensity b E x₀ ≤ minimizerPerimeterUpperConst m`. -/
theorem IsLocalPerimeterMinimizer.exists_tendsto_perimeter_ratio_nhdsGT_zero {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} (hx₀ : x₀ ∈ Ω) :
    ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧ θ₀ ≤ minimizerPerimeterUpperConst m ∧
      Tendsto (fun r ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
        (𝓝[>] 0) (𝓝 θ₀) := by
  obtain ⟨r₀, hr₀, hcb₀⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hmin.isOpen_domain.mem_nhds hx₀)
  let f : ℝ → ℝ := fun r ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal
  let S : Set ℝ := f '' Ioo 0 r₀
  have hS_ne : S.Nonempty := ⟨f (r₀ / 2), r₀ / 2, ⟨half_pos hr₀, half_lt_self hr₀⟩, rfl⟩
  have hS_bdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact mul_nonneg (zpow_nonneg hr.1.le _) ENNReal.toReal_nonneg
  let θ₀ : ℝ := sInf S
  have ht : Tendsto f (𝓝[>] 0) (𝓝 θ₀) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
      exact ha.trans_le (csInf_le hS_bdd ⟨r, hr, rfl⟩)
    · intro M hM
      obtain ⟨_, ⟨r₁, hr₁, rfl⟩, hlt⟩ := (csInf_lt_iff hS_bdd hS_ne).mp hM
      filter_upwards [Ioo_mem_nhdsGT hr₁.1] with r hr
      have hcb_r₁ : closedBall x₀ r₁ ⊆ Ω := (closedBall_subset_closedBall hr₁.2.le).trans hcb₀
      exact (hmin.perimeter_ratio_le hr.1 hr.2.le hcb_r₁).trans_lt hlt
  have hθ₀_nn : 0 ≤ θ₀ :=
    le_csInf hS_ne (by rintro _ ⟨r, hr, rfl⟩; exact mul_nonneg (zpow_nonneg hr.1.le _) ENNReal.toReal_nonneg)
  have hθ₀_up : θ₀ ≤ minimizerPerimeterUpperConst m := by
    have hr_half : r₀ / 2 ∈ Ioo 0 r₀ := ⟨half_pos hr₀, half_lt_self hr₀⟩
    have hcb_half : closedBall x₀ (r₀ / 2) ⊆ Ω :=
      (closedBall_subset_closedBall (half_lt_self hr₀).le).trans hcb₀
    have hf_le : f (r₀ / 2) ≤ minimizerPerimeterUpperConst m := by
      dsimp [f]
      calc
        (r₀ / 2) ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ (r₀ / 2))).toReal
          ≤ (r₀ / 2) ^ (-(m : ℤ)) * (minimizerPerimeterUpperConst m * (r₀ / 2) ^ m) :=
            mul_le_mul_of_nonneg_left
              (hmin.variationalPerimeter_ball_toReal_le (half_pos hr₀) hcb_half)
              (zpow_nonneg (half_pos hr₀).le _)
        _ = minimizerPerimeterUpperConst m := by
            rw [zpow_neg, zpow_natCast]
            have hne : (r₀ / 2) ^ m ≠ 0 := pow_ne_zero m (half_pos hr₀).ne'
            field_simp
    exact (csInf_le hS_bdd ⟨r₀ / 2, hr_half, rfl⟩).trans hf_le
  exact ⟨θ₀, hθ₀_nn, hθ₀_up, ht⟩

theorem IsLocalPerimeterMinimizer.tendsto_perimeterDensity {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} (hx₀ : x₀ ∈ Ω) :
    Tendsto (fun r ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
      (𝓝[>] 0) (𝓝 (perimeterDensity b E x₀)) := by
  obtain ⟨θ₀, -, -, ht⟩ := hmin.exists_tendsto_perimeter_ratio_nhdsGT_zero hx₀
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  unfold perimeterDensity
  rwa [ht.limUnder_eq]

theorem IsLocalPerimeterMinimizer.perimeterDensity_nonneg {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} (hx₀ : x₀ ∈ Ω) :
    0 ≤ perimeterDensity b E x₀ := by
  obtain ⟨θ₀, h0, -, ht⟩ := hmin.exists_tendsto_perimeter_ratio_nhdsGT_zero hx₀
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  rwa [tendsto_nhds_unique (hmin.tendsto_perimeterDensity hx₀) ht]

theorem IsLocalPerimeterMinimizer.perimeterDensity_le_upperConst {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} (hx₀ : x₀ ∈ Ω) :
    perimeterDensity b E x₀ ≤ minimizerPerimeterUpperConst m := by
  obtain ⟨θ₀, -, hup, ht⟩ := hmin.exists_tendsto_perimeter_ratio_nhdsGT_zero hx₀
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  rwa [tendsto_nhds_unique (hmin.tendsto_perimeterDensity hx₀) ht]

theorem IsLocalPerimeterMinimizer.perimeterDensity_le_ratio {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω) :
    perimeterDensity b E x₀ ≤
      r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal := by
  have hx₀ : x₀ ∈ Ω := hsub (mem_closedBall_self hr.le)
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  refine le_of_tendsto (hmin.tendsto_perimeterDensity hx₀) ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with s hs
  exact hmin.perimeter_ratio_le hs.1 hs.2.le hsub

theorem IsLocalPerimeterMinimizer.perimeterDensity_ge_lowerConst {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)}
    (hx₀_bdry : x₀ ∈ measureTheoreticBoundary E) (hx₀_Ω : x₀ ∈ Ω) :
    minimizerPerimeterLowerConst m ≤ perimeterDensity b E x₀ := by
  obtain ⟨r₀, hr₀, hcb₀⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hmin.isOpen_domain.mem_nhds hx₀_Ω)
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  refine ge_of_tendsto (hmin.tendsto_perimeterDensity hx₀_Ω) ?_
  filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
  have hcb : closedBall x₀ r ⊆ Ω := (closedBall_subset_closedBall hr.2.le).trans hcb₀
  have hge := hmin.variationalPerimeter_ball_toReal_ge hx₀_bdry hr.1 hcb
  calc
    minimizerPerimeterLowerConst m
      = r ^ (-(m : ℤ)) * (minimizerPerimeterLowerConst m * r ^ m) := by
          rw [zpow_neg, zpow_natCast]
          have hne : r ^ m ≠ 0 := pow_ne_zero m hr.1.ne'
          field_simp
    _ ≤ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal :=
        mul_le_mul_of_nonneg_left hge (zpow_nonneg hr.1.le _)

/-- Asymptotic perimeter density at infinity (`R → ∞`) for global perimeter minimizers:
`lim_{R → ∞} R ^ (-m) * (variationalPerimeter b E (ball x₀ R)).toReal`. -/
def perimeterInfinityDensity {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (E : Set (Space (m + 1))) (x₀ : Space (m + 1)) : ℝ :=
  limUnder atTop (fun R : ℝ ↦ R ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ R)).toReal)

/-- For a global perimeter minimizer on `univ`, `R ^ (-m) * P(E, ball x₀ R)` converges as
`R → ∞` to a finite limit bounded by `minimizerPerimeterUpperConst m`. -/
theorem IsLocalPerimeterMinimizer.exists_tendsto_perimeter_ratio_atTop {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) (x₀ : Space (m + 1)) :
    ∃ θ_inf : ℝ, 0 ≤ θ_inf ∧ θ_inf ≤ minimizerPerimeterUpperConst m ∧
      Tendsto (fun R ↦ R ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ R)).toReal)
        atTop (𝓝 θ_inf) := by
  let f : ℝ → ℝ := fun R ↦ R ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ R)).toReal
  let S : Set ℝ := f '' Ioi 0
  have hS_ne : S.Nonempty := ⟨f 1, 1, zero_lt_one, rfl⟩
  have hf_le (R : ℝ) (hR : 0 < R) : f R ≤ minimizerPerimeterUpperConst m := by
    dsimp [f]
    calc
      R ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ R)).toReal
        ≤ R ^ (-(m : ℤ)) * (minimizerPerimeterUpperConst m * R ^ m) :=
          mul_le_mul_of_nonneg_left
            (hmin.variationalPerimeter_ball_toReal_le hR (subset_univ _))
            (zpow_nonneg hR.le _)
      _ = minimizerPerimeterUpperConst m := by
          rw [zpow_neg, zpow_natCast]
          have hne : R ^ m ≠ 0 := pow_ne_zero m hR.ne'
          field_simp
  have hS_bdd : BddAbove S := by
    refine ⟨minimizerPerimeterUpperConst m, ?_⟩
    rintro _ ⟨R, hR, rfl⟩
    exact hf_le R hR
  let θ_inf : ℝ := sSup S
  have ht : Tendsto f atTop (𝓝 θ_inf) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨_, ⟨R₁, hR₁, rfl⟩, hgt⟩ := (lt_csSup_iff hS_bdd hS_ne).mp ha
      filter_upwards [eventually_ge_atTop R₁] with R hR
      exact hgt.trans_le (hmin.perimeter_ratio_le hR₁ hR (subset_univ _))
    · intro M hM
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact (le_csSup hS_bdd ⟨R, hR, rfl⟩).trans_lt hM
  have h0 : 0 ≤ θ_inf :=
    (show 0 ≤ f 1 by dsimp [f]; positivity).trans (le_csSup hS_bdd ⟨1, zero_lt_one, rfl⟩)
  have hup : θ_inf ≤ minimizerPerimeterUpperConst m := by
    refine csSup_le hS_ne ?_
    rintro _ ⟨R, hR, rfl⟩
    exact hf_le R hR
  exact ⟨θ_inf, h0, hup, ht⟩

theorem IsLocalPerimeterMinimizer.tendsto_perimeterInfinityDensity {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) (x₀ : Space (m + 1)) :
    Tendsto (fun R ↦ R ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ R)).toReal)
      atTop (𝓝 (perimeterInfinityDensity b E x₀)) := by
  obtain ⟨θ_inf, -, -, ht⟩ := hmin.exists_tendsto_perimeter_ratio_atTop x₀
  unfold perimeterInfinityDensity
  rwa [ht.limUnder_eq]

theorem IsLocalPerimeterMinimizer.perimeterInfinityDensity_nonneg {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) (x₀ : Space (m + 1)) :
    0 ≤ perimeterInfinityDensity b E x₀ := by
  obtain ⟨θ_inf, h0, -, ht⟩ := hmin.exists_tendsto_perimeter_ratio_atTop x₀
  rwa [tendsto_nhds_unique (hmin.tendsto_perimeterInfinityDensity x₀) ht]

theorem IsLocalPerimeterMinimizer.perimeterInfinityDensity_le_upperConst {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) (x₀ : Space (m + 1)) :
    perimeterInfinityDensity b E x₀ ≤ minimizerPerimeterUpperConst m := by
  obtain ⟨θ_inf, -, hup, ht⟩ := hmin.exists_tendsto_perimeter_ratio_atTop x₀
  rwa [tendsto_nhds_unique (hmin.tendsto_perimeterInfinityDensity x₀) ht]

theorem IsLocalPerimeterMinimizer.ratio_le_perimeterInfinityDensity {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) (x₀ : Space (m + 1)) {r : ℝ} (hr : 0 < r) :
    r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal ≤
      perimeterInfinityDensity b E x₀ := by
  refine ge_of_tendsto (hmin.tendsto_perimeterInfinityDensity x₀) ?_
  filter_upwards [eventually_ge_atTop r] with R hR
  exact hmin.perimeter_ratio_le hr hR (subset_univ _)

theorem IsLocalPerimeterMinimizer.perimeterInfinityDensity_ge_lowerConst {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) {x₀ : Space (m + 1)}
    (hx₀ : x₀ ∈ measureTheoreticBoundary E) :
    minimizerPerimeterLowerConst m ≤ perimeterInfinityDensity b E x₀ := by
  have hge := hmin.variationalPerimeter_ball_toReal_ge hx₀ zero_lt_one (subset_univ _)
  have h1 : minimizerPerimeterLowerConst m ≤
      (1 : ℝ) ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ 1)).toReal := by
    simpa using hge
  exact h1.trans (hmin.ratio_le_perimeterInfinityDensity x₀ zero_lt_one)

/-! ### 3. Constant Perimeter Density Implies Cone Invariance (BV10.3) -/

/-- If `r ↦ r ^ (-m) * P(E, ball x₀ r)` is constant on `Ioo 0 R₀` (`ball x₀ R₀ ⊆ Ω`), then for any
Radon perimeter representation `(μ, ν)` on `ball x₀ R₀`, every concentric sphere inside `ball x₀ R₀`
has zero `μ`-mass and `inner ℝ (x - x₀) (ν x) = 0` `μ`-almost everywhere on `ball x₀ R₀`. -/
theorem IsLocalPerimeterMinimizer.sphere_zero_and_ae_inner_polar_eq_zero_of_constant_ratio {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} {R₀ θ : ℝ}
    (hR₀ : 0 < R₀) (hsub : ball x₀ R₀ ⊆ Ω)
    (hconst : ∀ r ∈ Ioo 0 R₀,
      r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal = θ)
    (μ : Measure (Space (m + 1))) {ν : Space (m + 1) → Space (m + 1)}
    (hμ_open : ∀ U, IsOpen U → U ⊆ ball x₀ R₀ → μ U = variationalPerimeter b E U)
    (hν : Integrable ν (μ.restrict (ball x₀ R₀)))
    (hνunit : ∀ᵐ x ∂μ.restrict (ball x₀ R₀), ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport F ⊆ ball x₀ R₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict (ball x₀ R₀)) :
    (∀ r ∈ Ioo 0 R₀, μ (sphere x₀ r) = 0) ∧
      (∀ᵐ x ∂μ.restrict (ball x₀ R₀), inner ℝ (x - x₀) (ν x) = 0) := by
  have hμR₀_lt : μ (ball x₀ R₀) < ⊤ := by
    have heq : (∫⁻ _, (1 : ℝ≥0∞) ∂(μ.restrict (ball x₀ R₀))) =
        ∫⁻ x, ‖ν x‖ₑ ∂(μ.restrict (ball x₀ R₀)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hνunit] with x hx
      simp [← ofReal_norm, hx]
    rw [lintegral_const, one_mul, Measure.restrict_apply_univ] at heq
    exact heq ▸ hν.2
  have hpair {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hRR₀ : R < R₀) :
      μ (sphere x₀ r) = 0 ∧
        ∀ᵐ x ∂μ.restrict (ball x₀ R \ closedBall x₀ r), inner ℝ (x - x₀) (ν x) = 0 := by
    have hid := hmin.perimeter_monotonicity_ball_sphere_identity hr hrR hRR₀ hsub μ hν hνunit hdist
    have hμ_r : μ.real (ball x₀ r) = (variationalPerimeter b E (ball x₀ r)).toReal := by
      simp [Measure.real, hμ_open (ball x₀ r) isOpen_ball (ball_subset_ball (hrR.trans hRR₀).le)]
    have hμ_R : μ.real (ball x₀ R) = (variationalPerimeter b E (ball x₀ R)).toReal := by
      simp [Measure.real, hμ_open (ball x₀ R) isOpen_ball (ball_subset_ball hRR₀.le)]
    have hlhs : R ^ (-(m : ℤ)) * μ.real (ball x₀ R) - r ^ (-(m : ℤ)) * μ.real (ball x₀ r) = 0 := by
      rw [hμ_R, hμ_r, hconst R ⟨hr.trans hrR, hRR₀⟩, hconst r ⟨hr, hrR.trans hRR₀⟩, sub_self]
    rw [hlhs] at hid
    let A : Set (Space (m + 1)) := ball x₀ R \ closedBall x₀ r
    have hA_meas : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
    have hA_sub : A ⊆ ball x₀ R₀ := sdiff_subset.trans (ball_subset_ball hRR₀.le)
    let g : Space (m + 1) → ℝ := fun x ↦ (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ (m + 2)
    have hs_nn : 0 ≤ r ^ (-(m : ℤ)) * μ.real (sphere x₀ r) :=
      mul_nonneg (zpow_nonneg hr.le _) measureReal_nonneg
    have hint_nn : 0 ≤ ∫ x in A, g x ∂μ :=
      integral_nonneg fun x ↦ div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
    have hs_zero : r ^ (-(m : ℤ)) * μ.real (sphere x₀ r) = 0 := by linarith
    have hint_zero : (∫ x in A, g x ∂μ) = 0 := by linarith
    have hsph_real_zero : μ.real (sphere x₀ r) = 0 :=
      (mul_eq_zero.mp hs_zero).resolve_left (zpow_pos hr _).ne'
    have hsph_fin : μ (sphere x₀ r) ≠ ⊤ :=
      ((measure_mono (sphere_subset_closedBall.trans
        (closedBall_subset_ball (hrR.trans hRR₀)))).trans_lt hμR₀_lt).ne
    have hsph_zero : μ (sphere x₀ r) = 0 := by
      by_contra hne
      exact (ENNReal.toReal_pos hne hsph_fin).ne' hsph_real_zero
    have hg_int : IntegrableOn g A μ := by
      have hres_eq : μ.restrict A = (μ.restrict (ball x₀ R₀)).restrict A := by
        rw [Measure.restrict_restrict hA_meas, inter_eq_left.mpr hA_sub]
      change Integrable g (μ.restrict A)
      rw [hres_eq]
      let _ : IsFiniteMeasure ((μ.restrict (ball x₀ R₀)).restrict A) := ⟨by
        rw [Measure.restrict_apply_univ, Measure.restrict_apply hA_meas]
        exact (measure_mono inter_subset_right).trans_lt hμR₀_lt⟩
      have hg_meas : AEStronglyMeasurable g ((μ.restrict (ball x₀ R₀)).restrict A) := by
        dsimp only [g]
        simp_rw [div_eq_mul_inv]
        exact ((((continuous_id.sub continuous_const).aestronglyMeasurable.inner
          hν.aestronglyMeasurable.restrict).pow 2).mul
            ((((measurable_id.sub measurable_const).norm.pow_const (m + 2)).inv)
              |>.aestronglyMeasurable))
      refine Integrable.of_bound hg_meas ((r ^ m)⁻¹) ?_
      filter_upwards [ae_restrict_of_ae hνunit, ae_restrict_mem hA_meas] with x hx_u hxA
      have hr_lt : r < ‖x - x₀‖ :=
        lt_of_not_ge (by simpa [mem_closedBall, dist_eq_norm] using hxA.2)
      have hρ_pos : 0 < ‖x - x₀‖ := hr.trans hr_lt
      have hcs : (inner ℝ (x - x₀) (ν x)) ^ 2 ≤ ‖x - x₀‖ ^ 2 := by
        have habs : |inner ℝ (x - x₀) (ν x)| ≤ ‖x - x₀‖ := by
          calc
            |inner ℝ (x - x₀) (ν x)| ≤ ‖x - x₀‖ * ‖ν x‖ := abs_real_inner_le_norm _ _
            _ = ‖x - x₀‖ := by rw [hx_u, mul_one]
        simpa only [sq_abs] using sq_le_sq.mpr (by rwa [abs_of_pos hρ_pos])
      dsimp only [g]
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg hρ_pos.le _))]
      have hp : ‖x - x₀‖ ^ (m + 2) = ‖x - x₀‖ ^ m * ‖x - x₀‖ ^ 2 := by rw [← pow_add]
      rw [hp, div_mul_eq_div_div, div_le_iff₀ (sq_pos_of_pos hρ_pos)]
      calc
        (inner ℝ (x - x₀) (ν x)) ^ 2 / ‖x - x₀‖ ^ m
          ≤ ‖x - x₀‖ ^ 2 / ‖x - x₀‖ ^ m :=
            div_le_div_of_nonneg_right hcs (pow_nonneg hρ_pos.le m)
        _ = (‖x - x₀‖ ^ m)⁻¹ * ‖x - x₀‖ ^ 2 := by ring
        _ ≤ (r ^ m)⁻¹ * ‖x - x₀‖ ^ 2 :=
            mul_le_mul_of_nonneg_right
              (inv_anti₀ (pow_pos hr m) (pow_le_pow_left₀ hr.le hr_lt.le m)) (sq_nonneg _)
    have hae_g0 := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x ↦ div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _))
      hg_int).mp hint_zero
    refine ⟨hsph_zero, ?_⟩
    filter_upwards [hae_g0, ae_restrict_mem hA_meas] with x hxg hxA
    have hr_lt : r < ‖x - x₀‖ :=
      lt_of_not_ge (by simpa [mem_closedBall, dist_eq_norm] using hxA.2)
    have hden_ne : ‖x - x₀‖ ^ (m + 2) ≠ 0 := pow_ne_zero _ (hr.trans hr_lt).ne'
    have hsq0 : (inner ℝ (x - x₀) (ν x)) ^ 2 = 0 := (div_eq_zero_iff.mp hxg).resolve_right hden_ne
    exact sq_eq_zero_iff.mp hsq0
  refine ⟨fun r hr ↦ ?_, ?_⟩
  · exact (hpair hr.1 (show r < (r + R₀) / 2 by linarith [hr.2])
      (show (r + R₀) / 2 < R₀ by linarith [hr.2])).1
  · let B_seq : ℕ → Set (Space (m + 1)) := fun k ↦
      ball x₀ ((1 - 1 / ((k : ℝ) + 3)) * R₀) \ closedBall x₀ (R₀ / ((k : ℝ) + 3))
    have hloc (k : ℕ) : ∀ᵐ x ∂μ.restrict (B_seq k), inner ℝ (x - x₀) (ν x) = 0 := by
      have hr_pos : 0 < R₀ / ((k : ℝ) + 3) := by positivity
      have hrR : R₀ / ((k : ℝ) + 3) < (1 - 1 / ((k : ℝ) + 3)) * R₀ := by
        have h1 : 2 / ((k : ℝ) + 3) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
        have hmul := mul_lt_mul_of_pos_right h1 hR₀
        have halg : 2 / ((k : ℝ) + 3) * R₀ =
            R₀ / ((k : ℝ) + 3) + (1 - (1 - 1 / ((k : ℝ) + 3))) * R₀ := by ring
        linarith
      have hRR₀ : (1 - 1 / ((k : ℝ) + 3)) * R₀ < R₀ := by
        have hpos : 0 < (1 / ((k : ℝ) + 3)) * R₀ := by positivity
        have halg : (1 - 1 / ((k : ℝ) + 3)) * R₀ = R₀ - (1 / ((k : ℝ) + 3)) * R₀ := by ring
        linarith
      exact (hpair hr_pos hrR hRR₀).2
    have hall : ∀ᵐ x ∂μ.restrict (⋃ k : ℕ, B_seq k), inner ℝ (x - x₀) (ν x) = 0 :=
      (ae_restrict_iUnion_iff B_seq _).mpr hloc
    have hiUnion : (⋃ k : ℕ, B_seq k) = ball x₀ R₀ \ {x₀} := by
      ext x
      simp only [mem_iUnion, B_seq, Set.mem_sdiff, mem_ball, mem_closedBall, mem_singleton_iff,
        not_le]
      constructor
      · rintro ⟨k, hlt, hgt⟩
        have hpos : 0 < (1 / ((k : ℝ) + 3)) * R₀ := by positivity
        have hr_pos : 0 < R₀ / ((k : ℝ) + 3) := by positivity
        have halg : (1 - 1 / ((k : ℝ) + 3)) * R₀ = R₀ - (1 / ((k : ℝ) + 3)) * R₀ := by ring
        refine ⟨by linarith, fun heq ↦ ?_⟩
        subst heq
        simp only [dist_self] at hgt
        exact not_lt_of_ge hr_pos.le hgt
      · rintro ⟨hlt, hne⟩
        have hd_pos : 0 < dist x x₀ := dist_pos.mpr hne
        obtain ⟨k₁, hk₁⟩ := exists_nat_one_div_lt (div_pos (sub_pos.mpr hlt) hR₀)
        obtain ⟨k₂, hk₂⟩ := exists_nat_one_div_lt (div_pos hd_pos hR₀)
        let k := max k₁ k₂
        refine ⟨k, ?_, ?_⟩
        · have hk_ge : (k₁ : ℝ) + 1 ≤ (k : ℝ) + 3 := by
            have : k₁ ≤ k := le_max_left k₁ k₂
            exact_mod_cast (by omega : k₁ + 1 ≤ k + 3)
          have hle : 1 / ((k : ℝ) + 3) < (R₀ - dist x x₀) / R₀ :=
            lt_of_le_of_lt (div_le_div_of_nonneg_left zero_le_one (by positivity) hk_ge) hk₁
          have hmul := mul_lt_mul_of_pos_right hle hR₀
          rw [div_mul_cancel₀ _ hR₀.ne'] at hmul
          have halg : (1 - 1 / ((k : ℝ) + 3)) * R₀ = R₀ - 1 / ((k : ℝ) + 3) * R₀ := by ring
          linarith
        · have hk_ge : (k₂ : ℝ) + 1 ≤ (k : ℝ) + 3 := by
            have : k₂ ≤ k := le_max_right k₁ k₂
            exact_mod_cast (by omega : k₂ + 1 ≤ k + 3)
          have hle : 1 / ((k : ℝ) + 3) < dist x x₀ / R₀ :=
            lt_of_le_of_lt (div_le_div_of_nonneg_left zero_le_one (by positivity) hk_ge) hk₂
          have hmul := mul_lt_mul_of_pos_right hle hR₀
          rw [div_mul_cancel₀ _ hR₀.ne'] at hmul
          simpa [div_eq_inv_mul] using hmul
    rw [hiUnion] at hall
    rw [ae_restrict_iff' measurableSet_ball]
    rw [ae_restrict_iff' (measurableSet_ball.diff (measurableSet_singleton x₀))] at hall
    filter_upwards [hall] with x hx hxb
    by_cases hxx₀ : x = x₀
    · subst hxx₀
      simp
    · exact hx ⟨hxb, hxx₀⟩

private theorem integral_indicator_divergence_smul_id_eq_zero_of_constant_ratio {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) {θ : ℝ}
    (hconst : ∀ r > 0, r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball 0 r)).toReal = θ)
    {ψ : Space (m + 1) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b (fun y ↦ ψ y • y) x) = 0 := by
  obtain ⟨n, hn⟩ := compact_subset_perimeter_ball hψc
  let R₀ : ℝ := (n : ℝ) + 1
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  obtain ⟨δ, μ, ν, hδ, -, hfin, hzero, hμ_open, hν_int, hν_unit, hdist⟩ :=
    hmin.exists_ball_radon_measure hR₀ (subset_univ (closedBall (0 : Space (m + 1)) R₀))
  let _ : IsFiniteMeasure μ := hfin
  have hres_self : μ.restrict (ball 0 (R₀ + δ)) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hzero)
  have hpolar_zero := (hmin.sphere_zero_and_ae_inner_polar_eq_zero_of_constant_ratio
    (x₀ := 0) (R₀ := R₀ + δ) (by linarith) (subset_univ _)
    (fun r hr ↦ hconst r hr.1) μ hμ_open
    (by rwa [hres_self]) (by rwa [hres_self])
    (fun F hF hs ↦ by rw [hres_self]; exact hdist F hF hs)).2
  rw [hres_self] at hpolar_zero
  let F_fn : Space (m + 1) → Space (m + 1) := fun y ↦ ψ y • y
  have hF_cd : ContDiff ℝ 1 F_fn := hψ.smul contDiff_id
  have hF_ts : tsupport F_fn ⊆ ball 0 (R₀ + δ) :=
    (tsupport_smul_subset_left ψ id).trans (hn.trans (ball_subset_ball (by dsimp [R₀]; linarith)))
  have hF_c : HasCompactSupport F_fn := hψc.smul_right
  let F_cc : C_c(Space (m + 1), Space (m + 1)) := ⟨⟨F_fn, hF_cd.continuous⟩, hF_c⟩
  have hibp := hdist F_cc hF_cd hF_ts
  have hrhs_zero : (∫ x, inner ℝ (F_cc x) (ν x) ∂μ) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hpolar_zero] with x hx
    change inner ℝ (ψ x • x) (ν x) = 0
    rw [real_inner_smul_left]
    simp only [sub_zero] at hx
    rw [hx, mul_zero]
  rw [hrhs_zero] at hibp
  exact neg_eq_zero.mp hibp

/-- Cone invariance at the origin (BV10.3): if `E` is a global perimeter minimizer on `univ` and
`r ↦ r ^ (-m) * P(E, ball 0 r)` is constant on `(0, ∞)`, then for every `a > 0`, `E` is
Lebesgue-a.e. invariant under dilation by `a`. -/
theorem IsLocalPerimeterMinimizer.ae_mem_smul_iff_of_constant_perimeter_ratio {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) {θ : ℝ}
    (hconst : ∀ r > 0, r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball 0 r)).toReal = θ)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ y ∂volume, y ∈ E ↔ a • y ∈ E := by
  let χ : Space (m + 1) → ℝ := E.indicator (fun _ ↦ (1 : ℝ))
  have hχ_meas : Measurable χ := measurable_const.indicator hmin.measurableSet
  let diff_fn : Space (m + 1) → ℝ := fun y ↦ χ (a • y) - χ y
  have hdiff_loc : LocallyIntegrable diff_fn volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    let _ : IsFiniteMeasure (volume.restrict K) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hK.measure_lt_top⟩
    have hm : Measurable diff_fn := (hχ_meas.comp (measurable_id.const_smul a)).sub hχ_meas
    refine Integrable.of_bound hm.aestronglyMeasurable 2 (Eventually.of_forall fun y ↦ ?_)
    have h1 : χ (a • y) ∈ Icc (0 : ℝ) 1 := by by_cases h : a • y ∈ E <;> simp [χ, h]
    have h2 : χ y ∈ Icc (0 : ℝ) 1 := by by_cases h : y ∈ E <;> simp [χ, h]
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  have hae_zero : diff_fn =ᵐ[volume] 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hdiff_loc fun ψ hψ hψc ↦ ?_
    obtain ⟨n_ψ, hn_ψ⟩ := compact_subset_perimeter_ball hψc
    let R_ψ : ℝ := (n_ψ : ℝ) + 1
    have hR_ψ : 0 < R_ψ := by dsimp [R_ψ]; positivity
    let g : ℝ → Space (m + 1) → ℝ := fun t x ↦ (t ^ (m + 1))⁻¹ * ψ (t⁻¹ • x)
    let g' : ℝ → Space (m + 1) → ℝ := fun t x ↦
      -(t ^ (m + 2))⁻¹ *
        (((m + 1 : ℕ) : ℝ) * ψ (t⁻¹ • x) + t⁻¹ * fderiv ℝ ψ (t⁻¹ • x) x)
    let H : ℝ → ℝ := fun t ↦ ∫ x, χ x * g t x
    have hH_smul {t : ℝ} (ht : 0 < t) : H t = ∫ y, χ (t • y) * ψ y := by
      have hdil := Measure.integral_comp_smul (μ := volume)
        (f := fun x : Space (m + 1) ↦ χ x * ψ (t⁻¹ • x)) t
      simp only [Space, finrank_euclideanSpace_fin, abs_inv, abs_pow, abs_of_pos ht,
        smul_eq_mul] at hdil
      have hlhs : (fun y : Space (m + 1) ↦ χ (t • y) * ψ (t⁻¹ • (t • y))) =
          fun y ↦ χ (t • y) * ψ y := by
        funext y
        simp [smul_smul, inv_mul_cancel₀ ht.ne']
      rw [hlhs] at hdil
      rw [hdil]
      dsimp only [H, g]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      ring
    have hg_deriv {t : ℝ} (ht : 0 < t) (x : Space (m + 1)) :
        HasDerivAt (fun s ↦ g s x) (g' t x) t := by
      have hp : HasDerivAt (fun s : ℝ ↦ (s ^ (m + 1))⁻¹)
          (-(((m + 1 : ℕ) : ℝ) * t ^ m) / (t ^ (m + 1)) ^ 2) t := by
        convert (hasDerivAt_pow (m + 1) t).inv (pow_ne_zero _ ht.ne') using 1
        simp
      have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹ • x) ((-(t ^ 2)⁻¹) • x) t :=
        (hasDerivAt_inv ht.ne').smul_const x
      have hψ_comp :=
        (hψ.differentiable (by simp) (t⁻¹ • x)).hasFDerivAt.comp_hasDerivAt t hinv
      refine (hp.mul hψ_comp).congr_deriv ?_
      dsimp only [g', Function.comp_def]
      rw [map_smul, smul_eq_mul]
      have ht_ne : t ≠ 0 := ht.ne'
      rw [show m + 2 = m + 1 + 1 by omega, pow_succ t (m + 1), pow_succ t m]
      field_simp
      ring
    have hH_deriv {t₀ : ℝ} (ht₀ : 0 < t₀) : HasDerivAt H 0 t₀ := by
      let K_ball : Set (Space (m + 1)) := closedBall 0 (2 * t₀ * R_ψ)
      have hK_comp : IsCompact K_ball := isCompact_closedBall 0 _
      let _ : IsFiniteMeasure (volume.restrict K_ball) := ⟨by
        rw [Measure.restrict_apply_univ]
        exact hK_comp.measure_lt_top⟩
      let J_set : Set ℝ := Icc (t₀ / 2) (2 * t₀)
      have hJ_pos {s : ℝ} (hs : s ∈ J_set) : 0 < s := (half_pos ht₀).trans_le hs.1
      have hg'_cont : ContinuousOn (fun p : ℝ × Space (m + 1) ↦ g' p.1 p.2)
          (J_set ×ˢ K_ball) := by
        intro p hp
        have hp_ne : p.1 ≠ 0 := (hJ_pos hp.1).ne'
        have harg : ContinuousAt (fun q : ℝ × Space (m + 1) ↦ q.1⁻¹ • q.2) p :=
          (continuousAt_fst.inv₀ hp_ne).smul continuousAt_snd
        have hψ_at : ContinuousAt (fun q : ℝ × Space (m + 1) ↦ ψ (q.1⁻¹ • q.2)) p :=
          hψ.continuous.continuousAt.comp harg
        have hfd_at : ContinuousAt
            (fun q : ℝ × Space (m + 1) ↦ fderiv ℝ ψ (q.1⁻¹ • q.2) q.2) p :=
          isBoundedBilinearMap_apply.continuous.continuousAt.comp
            ((((hψ.of_le (by simp)).continuous_fderiv one_ne_zero).continuousAt.comp harg).prodMk
              continuousAt_snd)
        exact ((((continuousAt_fst.pow (m + 2)).inv₀ (pow_ne_zero _ hp_ne)).neg).mul
          ((continuousAt_const.mul hψ_at).add
            ((continuousAt_fst.inv₀ hp_ne).mul hfd_at))).continuousWithinAt
      obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod hK_comp).exists_bound_of_continuousOn hg'_cont
      let M : ℝ := max M₀ 0
      have hg_vanish {s : ℝ} (hs : s ∈ Ioo (t₀ / 2) (2 * t₀)) {x : Space (m + 1)}
          (hx : x ∉ K_ball) : g s x = 0 ∧ g' s x = 0 := by
        have hs_pos : 0 < s := (half_pos ht₀).trans hs.1
        have hx_gt : 2 * t₀ * R_ψ < ‖x‖ :=
          by simpa [K_ball, mem_closedBall, dist_zero_right] using hx
        have hquot_gt : R_ψ < ‖s⁻¹ • x‖ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs_pos.le), ← div_eq_inv_mul,
            lt_div_iff₀ hs_pos]
          nlinarith [hs.2, hR_ψ]
        have hnot_ts : s⁻¹ • x ∉ tsupport ψ :=
          fun hh ↦ not_lt_of_ge (mem_ball_zero_iff.mp (hn_ψ hh)).le hquot_gt
        have hψ0 : ψ (s⁻¹ • x) = 0 := image_eq_zero_of_notMem_tsupport hnot_ts
        have hfd0 : fderiv ℝ ψ (s⁻¹ • x) = 0 := fderiv_of_notMem_tsupport ℝ hnot_ts
        simp [g, g', hψ0, hfd0]
      have hH_loc : ∀ᶠ s in 𝓝 t₀, H s = ∫ x in K_ball, χ x * g s x := by
        filter_upwards [Ioo_mem_nhds (half_lt_self ht₀) (by linarith : t₀ < 2 * t₀)] with s hs
        symm
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
        rw [(hg_vanish hs hx).1, mul_zero]
      have hg_cont (s : ℝ) : Continuous (g s) := by
        dsimp [g]
        exact continuous_const.mul (hψ.continuous.comp (continuous_id.const_smul s⁻¹))
      have hg'_t₀_cont : Continuous (g' t₀) := by
        dsimp [g']
        exact continuous_const.mul
          ((continuous_const.mul (hψ.continuous.comp (continuous_id.const_smul t₀⁻¹))).add
            (continuous_const.mul
              ((((hψ.of_le (by simp)).continuous_fderiv one_ne_zero).comp
                (continuous_id.const_smul t₀⁻¹)).clm_apply continuous_id)))
      obtain ⟨Mg₀, hMg₀⟩ := hK_comp.exists_bound_of_continuousOn (hg_cont t₀).continuousOn
      have hd_K : HasDerivAt (fun s ↦ ∫ x in K_ball, χ x * g s x)
          (∫ x in K_ball, χ x * g' t₀ x) t₀ := by
        refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict K_ball)
          (s := Ioo (t₀ / 2) (2 * t₀)) (bound := fun _ ↦ M)
          (F := fun s x ↦ χ x * g s x) (F' := fun s x ↦ χ x * g' s x)
          (Ioo_mem_nhds (half_lt_self ht₀) (by linarith))
          (Eventually.of_forall fun s ↦
            hχ_meas.aestronglyMeasurable.mul (hg_cont s).aestronglyMeasurable)
          (Integrable.of_bound
            (hχ_meas.aestronglyMeasurable.mul (hg_cont t₀).aestronglyMeasurable)
            (max Mg₀ 0)
            (by
              filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
              have hχx : ‖χ x‖ ≤ 1 := by by_cases h : x ∈ E <;> simp [χ, h]
              have hgx : ‖g t₀ x‖ ≤ max Mg₀ 0 := (hMg₀ x hx).trans (le_max_left Mg₀ 0)
              rw [norm_mul]
              exact (mul_le_mul hχx hgx (norm_nonneg _) zero_le_one).trans (by simp)))
          (hχ_meas.aestronglyMeasurable.mul hg'_t₀_cont.aestronglyMeasurable)
          ?_ (integrable_const _) ?_).2
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx s hs
          have hχx : ‖χ x‖ ≤ 1 := by by_cases h : x ∈ E <;> simp [χ, h]
          have hg'x : ‖g' s x‖ ≤ M :=
            (hM₀ (s, x) ⟨⟨hs.1.le, hs.2.le⟩, hx⟩).trans (le_max_left M₀ 0)
          rw [norm_mul]
          exact (mul_le_mul hχx hg'x (norm_nonneg _) zero_le_one).trans (by simp)
        · refine Eventually.of_forall fun x s hs ↦ ?_
          exact (hg_deriv ((half_pos ht₀).trans hs.1) x).const_mul (χ x)
      have hK_eq_full : (∫ x in K_ball, χ x * g' t₀ x) = ∫ x, χ x * g' t₀ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          rw [(hg_vanish ⟨half_lt_self ht₀, by linarith⟩ hx).2, mul_zero]
      let φ_t₀ : Space (m + 1) → ℝ := fun y ↦ ψ (t₀⁻¹ • y)
      have hφ_cd1 : ContDiff ℝ 1 φ_t₀ := (hψ.of_le (by simp)).comp (contDiff_id.const_smul t₀⁻¹)
      have hφ_c : HasCompactSupport φ_t₀ := by
        refine HasCompactSupport.of_support_subset_isCompact hK_comp fun x hx ↦ ?_
        by_contra hnot
        have hx_gt : 2 * t₀ * R_ψ < ‖x‖ :=
          by simpa [K_ball, mem_closedBall, dist_zero_right] using hnot
        have hquot_gt : R_ψ < ‖t₀⁻¹ • x‖ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht₀.le), ← div_eq_inv_mul,
            lt_div_iff₀ ht₀]
          nlinarith [ht₀, hR_ψ]
        exact hx (image_eq_zero_of_notMem_tsupport (f := ψ) fun hh ↦
          not_lt_of_ge (mem_ball_zero_iff.mp (hn_ψ hh)).le hquot_gt)
      have hg'_eq_div (x : Space (m + 1)) :
          g' t₀ x = -(t₀ ^ (m + 2))⁻¹ * fieldDivergence b (fun y ↦ φ_t₀ y • y) x := by
        have hdiv := fieldDivergence_smul_sub_const b (hφ_cd1.differentiable one_ne_zero x) 0
        simp only [sub_zero] at hdiv
        have hfd : fderiv ℝ φ_t₀ x x = t₀⁻¹ * fderiv ℝ ψ (t₀⁻¹ • x) x := by
          have hc := ((hψ.of_le (by simp)).differentiable one_ne_zero (t₀⁻¹ • x)).hasFDerivAt.comp x
            ((hasFDerivAt_id x).const_smul t₀⁻¹)
          change HasFDerivAt φ_t₀ _ x at hc
          rw [hc.fderiv]
          simp [smul_eq_mul]
        rw [hdiv, hfd]
      have hint_zero : (∫ x, χ x * g' t₀ x) = 0 := by
        have heq_fn : (fun x ↦ χ x * g' t₀ x) =
            fun x ↦ -(t₀ ^ (m + 2))⁻¹ * (χ x * fieldDivergence b (fun y ↦ φ_t₀ y • y) x) := by
          funext x
          rw [hg'_eq_div x]
          ring
        rw [heq_fn, integral_const_mul,
          integral_indicator_divergence_smul_id_eq_zero_of_constant_ratio hmin hconst hφ_cd1 hφ_c,
          mul_zero]
      rw [hK_eq_full, hint_zero] at hd_K
      exact hd_K.congr_of_eventuallyEq hH_loc
    have hexp_deriv (s : ℝ) : HasDerivAt (fun u ↦ H (Real.exp u)) 0 s := by
      change HasDerivAt (H ∘ Real.exp) 0 s
      simpa only [zero_mul] using (hH_deriv (Real.exp_pos s)).comp s (Real.hasDerivAt_exp s)
    have hHa_eq_H1 : H a = H 1 := by
      have hconst_exp := is_const_of_deriv_eq_zero
        (fun s ↦ (hexp_deriv s).differentiableAt) (fun s ↦ (hexp_deriv s).deriv) (Real.log a) 0
      simpa only [Real.exp_log ha, Real.exp_zero] using hconst_exp
    rw [hH_smul ha, hH_smul zero_lt_one] at hHa_eq_H1
    have hi_a : Integrable (fun y ↦ χ (a • y) * ψ y) volume := by
      refine (hψ.continuous.integrable_of_hasCompactSupport hψc).bdd_mul (c := 1)
        (hχ_meas.comp (measurable_id.const_smul a)).aestronglyMeasurable
        (Eventually.of_forall fun y ↦ ?_)
      by_cases h : a • y ∈ E <;> simp [χ, h]
    have hi_1 : Integrable (fun y ↦ χ y * ψ y) volume := by
      refine (hψ.continuous.integrable_of_hasCompactSupport hψc).bdd_mul (c := 1)
        hχ_meas.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
      by_cases h : y ∈ E <;> simp [χ, h]
    have hsub_zero : (∫ y, (χ (a • y) - χ y) * ψ y) = 0 := by
      simp_rw [sub_mul, one_smul] at hHa_eq_H1 ⊢
      rw [integral_sub hi_a hi_1, hHa_eq_H1, sub_self]
    simpa only [diff_fn, smul_eq_mul, mul_comm (ψ _)] using hsub_zero
  filter_upwards [hae_zero] with y hy
  change χ (a • y) - χ y = 0 at hy
  by_cases hyE : y ∈ E <;> by_cases hayE : a • y ∈ E <;> simp [χ, hyE, hayE] at hy ⊢

/-- Cone invariance at an arbitrary center `x₀` (BV10.3): if `E` is a global perimeter minimizer on
`univ` and `r ↦ r ^ (-m) * P(E, ball x₀ r)` is constant on `(0, ∞)`, then for every `a > 0`,
`x₀ + y ∈ E ↔ x₀ + a • y ∈ E` for Lebesgue-a.e. `y`. -/
theorem IsLocalPerimeterMinimizer.ae_mem_add_smul_iff_of_constant_perimeter_ratio {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) (x₀ : Space (m + 1)) {θ : ℝ}
    (hconst : ∀ r > 0, r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal = θ)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ y ∂volume, x₀ + y ∈ E ↔ x₀ + a • y ∈ E := by
  let T : Space (m + 1) → Space (m + 1) := fun y ↦ x₀ + (1 : ℝ) • y
  have hmin₀ : IsLocalPerimeterMinimizer b (T ⁻¹' E) univ := by
    simpa [T] using hmin.preimage_add_smul (by omega) x₀ zero_lt_one
  have hconst₀ (r : ℝ) (hr : 0 < r) :
      r ^ (-(m : ℤ)) * (variationalPerimeter b (T ⁻¹' E) (ball 0 r)).toReal = θ := by
    have hscale := variationalPerimeter_preimage_add_smul_ball (d := m + 1) (by omega) b E x₀ 0
      zero_lt_one (ρ := r)
    simp only [one_pow, inv_one, ENNReal.ofReal_one, one_mul, smul_zero, add_zero] at hscale
    rw [hscale]
    exact hconst r hr
  filter_upwards [hmin₀.ae_mem_smul_iff_of_constant_perimeter_ratio hconst₀ ha] with y hy
  simpa [T] using hy

/-- Strict pointwise cone invariance of `measureTheoreticInterior E` from a.e. cone invariance. -/
theorem mem_measureTheoreticInterior_smul_iff_of_ae_cone {d : ℕ} {E : Set (Space d)}
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ y ∂volume, y ∈ E ↔ a • y ∈ E)
    {a : ℝ} (ha : 0 < a) (y : Space d) :
    a • y ∈ measureTheoreticInterior E ↔ y ∈ measureTheoreticInterior E := by
  have hae : E =ᵐ[volume] (fun z : Space d ↦ (0 : Space d) + a • z) ⁻¹' E := by
    filter_upwards [hcone a ha] with z hz
    simp only [mem_preimage, zero_add]
    exact propext hz
  have heq := (measureTheoreticInterior_congr_ae hae).trans
    (measureTheoreticInterior_preimage_add_smul E 0 ha)
  have hmem := Set.ext_iff.mp heq y
  simpa only [mem_preimage, zero_add] using hmem.symm

/-- Strict pointwise cone invariance of `measureTheoreticExterior E` from a.e. cone invariance. -/
theorem mem_measureTheoreticExterior_smul_iff_of_ae_cone {d : ℕ} {E : Set (Space d)}
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ y ∂volume, y ∈ E ↔ a • y ∈ E)
    {a : ℝ} (ha : 0 < a) (y : Space d) :
    a • y ∈ measureTheoreticExterior E ↔ y ∈ measureTheoreticExterior E := by
  have hae : E =ᵐ[volume] (fun z : Space d ↦ (0 : Space d) + a • z) ⁻¹' E := by
    filter_upwards [hcone a ha] with z hz
    simp only [mem_preimage, zero_add]
    exact propext hz
  have heq := (measureTheoreticExterior_congr_ae hae).trans
    (measureTheoreticExterior_preimage_add_smul E 0 ha)
  have hmem := Set.ext_iff.mp heq y
  simpa only [mem_preimage, zero_add] using hmem.symm

/-- Strict pointwise cone invariance of `measureTheoreticBoundary E` from a.e. cone invariance. -/
theorem mem_measureTheoreticBoundary_smul_iff_of_ae_cone {d : ℕ} {E : Set (Space d)}
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ y ∂volume, y ∈ E ↔ a • y ∈ E)
    {a : ℝ} (ha : 0 < a) (y : Space d) :
    a • y ∈ measureTheoreticBoundary E ↔ y ∈ measureTheoreticBoundary E := by
  have hae : E =ᵐ[volume] (fun z : Space d ↦ (0 : Space d) + a • z) ⁻¹' E := by
    filter_upwards [hcone a ha] with z hz
    simp only [mem_preimage, zero_add]
    exact propext hz
  have heq := (measureTheoreticBoundary_congr_ae hae).trans
    (measureTheoreticBoundary_preimage_add_smul E 0 ha)
  have hmem := Set.ext_iff.mp heq y
  simpa only [mem_preimage, zero_add] using hmem.symm

/-! ### 4. Existence of Nontrivial Minimal Tangent Cones & Blowdown Cones (BV11) -/

private theorem tendsto_volume_inter_and_sdiff_ball_of_indicator_tendsto {d : ℕ}
    {A_seq : ℕ → Set (Space d)} {C : Set (Space d)}
    (hA : ∀ j, MeasurableSet (A_seq j)) (hC : MeasurableSet C) {R : ℝ}
    (ht : Tendsto (fun j ↦ ∫ y in closedBall (0 : Space d) R,
      ‖(A_seq j).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y‖)
      atTop (𝓝 0)) :
    Tendsto (fun j ↦ volume.real (A_seq j ∩ ball 0 R)) atTop (𝓝 (volume.real (C ∩ ball 0 R))) ∧
      Tendsto (fun j ↦ volume.real (ball 0 R \ A_seq j)) atTop (𝓝 (volume.real (ball 0 R \ C))) := by
  let _ : IsFiniteMeasure (volume.restrict (closedBall (0 : Space d) R)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall 0 R).measure_lt_top⟩
  let _ : IsFiniteMeasure (volume.restrict (ball (0 : Space d) R)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hvol_eq (S : Set (Space d)) (hS : MeasurableSet S) :
      volume.real (S ∩ ball 0 R) = ∫ y in ball (0 : Space d) R, S.indicator (fun _ ↦ (1 : ℝ)) y := by
    rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]
    simp [Measure.real, Measure.restrict_apply hS]
  have hsdiff_eq (S : Set (Space d)) : ball 0 R \ S = Sᶜ ∩ ball 0 R := by
    ext y
    simp [and_comm]
  constructor
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj
    rw [Real.dist_eq, ← Real.norm_eq_abs, hvol_eq (A_seq j) (hA j), hvol_eq C hC,
      ← integral_sub ((integrable_const (1 : ℝ)).indicator (hA j))
        ((integrable_const (1 : ℝ)).indicator hC)]
    have hcb_int : IntegrableOn
        (fun y ↦ ‖(A_seq j).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y‖)
        (closedBall 0 R) volume :=
      (((integrable_const (1 : ℝ)).indicator (hA j)).sub
        ((integrable_const (1 : ℝ)).indicator hC)).norm
    calc
      ‖∫ y in ball 0 R,
          ((A_seq j).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y)‖
        ≤ ∫ y in ball 0 R,
            ‖(A_seq j).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ y in closedBall 0 R,
            ‖(A_seq j).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y‖ :=
          setIntegral_mono_set hcb_int (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (Eventually.of_forall ball_subset_closedBall)
      _ < ε := hj
  · simp_rw [hsdiff_eq]
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj
    rw [Real.dist_eq, ← Real.norm_eq_abs, hvol_eq (A_seq j)ᶜ (hA j).compl, hvol_eq Cᶜ hC.compl,
      ← integral_sub ((integrable_const (1 : ℝ)).indicator (hA j).compl)
        ((integrable_const (1 : ℝ)).indicator hC.compl)]
    have hnorm_compl (y : Space d) :
        ‖(A_seq j)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y - Cᶜ.indicator (fun _ ↦ (1 : ℝ)) y‖ =
          ‖(A_seq j).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y‖ := by
      by_cases h1 : y ∈ A_seq j <;> by_cases h2 : y ∈ C <;> simp [h1, h2]
    have hcb_int : IntegrableOn
        (fun y ↦ ‖(A_seq j).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y‖)
        (closedBall 0 R) volume :=
      (((integrable_const (1 : ℝ)).indicator (hA j)).sub
        ((integrable_const (1 : ℝ)).indicator hC)).norm
    calc
      ‖∫ y in ball 0 R,
          ((A_seq j)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y - Cᶜ.indicator (fun _ ↦ (1 : ℝ)) y)‖
        ≤ ∫ y in ball 0 R,
            ‖(A_seq j)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y - Cᶜ.indicator (fun _ ↦ (1 : ℝ)) y‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ y in ball 0 R,
            ‖(A_seq j).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y‖ := by
          simp_rw [hnorm_compl]
      _ ≤ ∫ y in closedBall 0 R,
            ‖(A_seq j).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y‖ :=
          setIntegral_mono_set hcb_int (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (Eventually.of_forall ball_subset_closedBall)
      _ < ε := hj

private theorem ball_perimeter_eq_theta_mul_pow_of_ae_sphere_zero {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {C : Set (Space (m + 1))}
    (hC_min : IsLocalPerimeterMinimizer b C univ) {θ : ℝ}
    (μC : Measure (Space (m + 1))) [IsLocallyFiniteMeasure μC]
    (h_sph_eq : ∀ s : ℝ, 0 < s → μC (sphere 0 s) = 0 →
      (variationalPerimeter b C (ball 0 s)).toReal = θ * s ^ m)
    {R : ℝ} (hR : 0 < R) :
    (variationalPerimeter b C (ball 0 R)).toReal = θ * R ^ m := by
  have hae : ∀ᵐ s : ℝ ∂volume, 0 < s → μC (sphere 0 s) = 0 := ae_sphere_measure_eq_zero μC 0
  have hex_lo (k : ℕ) :
      ∃ s ∈ Ioo (max (R / 2) (R - 1 / ((k : ℝ) + 1))) R, μC (sphere 0 s) = 0 := by
    have hlb : max (R / 2) (R - 1 / ((k : ℝ) + 1)) < R :=
      max_lt (half_lt_self hR) (by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity])
    have hlb_pos : 0 < max (R / 2) (R - 1 / ((k : ℝ) + 1)) :=
      (half_pos hR).trans_le (le_max_left _ _)
    obtain ⟨s, hs, h0⟩ := exists_mem_Ioo_of_ae hlb hae
    exact ⟨s, hs, h0 (hlb_pos.trans hs.1)⟩
  choose s_lo hs_lo_mem hs_lo_sph using hex_lo
  have hs_lo_lim : Tendsto s_lo atTop (𝓝 R) := by
    have h1 : Tendsto (fun k : ℕ ↦ R - 1 / ((k : ℝ) + 1)) atTop (𝓝 R) := by
      simpa only [sub_zero] using
        tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
      (fun k ↦ (le_max_right _ _).trans (hs_lo_mem k).1.le)
      (fun k ↦ (hs_lo_mem k).2.le)
  have hex_hi (k : ℕ) :
      ∃ s ∈ Ioo R (R + 1 / ((k : ℝ) + 1)), μC (sphere 0 s) = 0 := by
    have hub : R < R + 1 / ((k : ℝ) + 1) := lt_add_of_pos_right R (by positivity)
    obtain ⟨s, hs, h0⟩ := exists_mem_Ioo_of_ae hub hae
    exact ⟨s, hs, h0 (hR.trans hs.1)⟩
  choose s_hi hs_hi_mem hs_hi_sph using hex_hi
  have hs_hi_lim : Tendsto s_hi atTop (𝓝 R) := by
    have h1 : Tendsto (fun k : ℕ ↦ R + 1 / ((k : ℝ) + 1)) atTop (𝓝 R) := by
      simpa only [add_zero] using
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
      (fun k ↦ (hs_hi_mem k).1.le)
      (fun k ↦ (hs_hi_mem k).2.le)
  have hle_k (k : ℕ) :
      θ * (s_lo k) ^ m ≤ (variationalPerimeter b C (ball 0 R)).toReal ∧
        (variationalPerimeter b C (ball 0 R)).toReal ≤ θ * (s_hi k) ^ m := by
    have hlo_pos : 0 < s_lo k := ((half_pos hR).trans_le (le_max_left _ _)).trans (hs_lo_mem k).1
    have hhi_pos : 0 < s_hi k := hR.trans (hs_hi_mem k).1
    have hPR_fin : variationalPerimeter b C (ball 0 R) ≠ ⊤ :=
      hC_min.perimeter_ball_ne_top 0 R hR (subset_univ _)
    have hPhi_fin : variationalPerimeter b C (ball 0 (s_hi k)) ≠ ⊤ :=
      hC_min.perimeter_ball_ne_top 0 (s_hi k) hhi_pos (subset_univ _)
    have hmono1 : (variationalPerimeter b C (ball 0 (s_lo k))).toReal ≤
        (variationalPerimeter b C (ball 0 R)).toReal :=
      ENNReal.toReal_mono hPR_fin (variationalPerimeter_mono b C (ball_subset_ball (hs_lo_mem k).2.le))
    have hmono2 : (variationalPerimeter b C (ball 0 R)).toReal ≤
        (variationalPerimeter b C (ball 0 (s_hi k))).toReal :=
      ENNReal.toReal_mono hPhi_fin (variationalPerimeter_mono b C (ball_subset_ball (hs_hi_mem k).1.le))
    rw [h_sph_eq (s_lo k) hlo_pos (hs_lo_sph k)] at hmono1
    rw [h_sph_eq (s_hi k) hhi_pos (hs_hi_sph k)] at hmono2
    exact ⟨hmono1, hmono2⟩
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_const_nhds.mul (hs_hi_lim.pow m))
      (Eventually.of_forall fun k ↦ (hle_k k).2)
  · exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul (hs_lo_lim.pow m)) tendsto_const_nhds
      (Eventually.of_forall fun k ↦ (hle_k k).1)

/-- Existence of nontrivial minimal tangent cones (BV11): at any measure-theoretic boundary point
`x₀ ∈ measureTheoreticBoundary E ∩ Ω` and along any positive scale sequence `r_seq → 0`, a
subsequence of `(E - x₀) / r_seq` converges in `L¹_loc` to a nontrivial global perimeter-minimizing
cone `C` whose ball perimeters satisfy `P(C, ball 0 R) = perimeterDensity b E x₀ * R ^ m` for
every `R > 0`. -/
theorem IsLocalPerimeterMinimizer.exists_tangent_cone {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)}
    (hx₀ : x₀ ∈ measureTheoreticBoundary E ∩ Ω)
    {r_seq : ℕ → ℝ} (hr_pos : ∀ j, 0 < r_seq j) (hr_lim : Tendsto r_seq atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (C : Set (Space (m + 1))),
      StrictMono φ ∧
      MeasurableSet C ∧
      IsLocalPerimeterMinimizer b C univ ∧
      (0 : Space (m + 1)) ∈ measureTheoreticBoundary C ∧
      volume C ≠ 0 ∧ volume Cᶜ ≠ 0 ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ y in K,
          ‖((fun z ↦ x₀ + r_seq (φ j) • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
            C.indicator (fun _ ↦ (1 : ℝ)) y‖)
          atTop (𝓝 0)) ∧
      (∀ R : ℝ, 0 < R →
        (variationalPerimeter b C (ball 0 R)).toReal = perimeterDensity b E x₀ * R ^ m) ∧
      (∀ a : ℝ, 0 < a → ∀ᵐ y ∂volume, y ∈ C ↔ a • y ∈ C) := by
  let E_seq : ℕ → Set (Space (m + 1)) := fun j ↦ (fun z ↦ x₀ + r_seq j • z) ⁻¹' E
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp hmin.isOpen_domain x₀ hx₀.2
  have hmin_ev (R : ℝ) (hR : 0 < R) :
      ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) (ball 0 R) := by
    have hprod_lim : Tendsto (fun j ↦ r_seq j * R) atTop (𝓝 0) := by
      simpa only [zero_mul] using hr_lim.mul_const R
    filter_upwards [hprod_lim.eventually (gt_mem_nhds hr₀)] with j hj
    refine (hmin.preimage_add_smul (by omega) x₀ (hr_pos j)).mono isOpen_ball ?_
    intro y hy
    apply hball₀
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (hr_pos j).le]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hy) (hr_pos j)).trans hj
  obtain ⟨φ, C, hφ, hC_min, ht, -, hP_sph⟩ :=
    exists_subsequence_univ_isLocalPerimeterMinimizer_of_eventually_ball (by omega) b E_seq hmin_ev
  have hE_seq_meas (j : ℕ) : MeasurableSet (E_seq (φ j)) :=
    hmin.measurableSet.preimage (by fun_prop)
  have h0_bdry : (0 : Space (m + 1)) ∈ measureTheoreticBoundary C := by
    intro R hR
    have hprod_lim : Tendsto (fun j ↦ r_seq (φ j) * R) atTop (𝓝 0) := by
      change Tendsto (fun j ↦ (r_seq ∘ φ) j * R) atTop (𝓝 0)
      simpa only [zero_mul] using (hr_lim.comp hφ.tendsto_atTop).mul_const R
    have hev_vol : ∀ᶠ j in atTop,
        minimizerVolumeDensityConst m * R ^ (m + 1) ≤ volume.real (E_seq (φ j) ∩ ball 0 R) ∧
          minimizerVolumeDensityConst m * R ^ (m + 1) ≤ volume.real (ball 0 R \ E_seq (φ j)) := by
      filter_upwards [hprod_lim.eventually (gt_mem_nhds hr₀)] with j hj
      have hj_min := hmin.preimage_add_smul (by omega) x₀ (hr_pos (φ j))
      have h0_j : (0 : Space (m + 1)) ∈ measureTheoreticBoundary (E_seq (φ j)) := by
        rw [mem_measureTheoreticBoundary_preimage_add_smul E x₀ 0 (hr_pos (φ j))]
        simpa using hx₀.1
      have hcb_j : closedBall (0 : Space (m + 1)) R ⊆ (fun z ↦ x₀ + r_seq (φ j) • z) ⁻¹' Ω := by
        intro y hy
        apply hball₀
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg (hr_pos (φ j)).le]
        have hy_le : ‖y‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hy
        exact (mul_le_mul_of_nonneg_left hy_le (hr_pos (φ j)).le).trans_lt hj
      exact ⟨hj_min.volume_inter_ball_ge h0_j hR hcb_j, hj_min.volume_sdiff_ball_ge h0_j hR hcb_j⟩
    have hvol_lim := tendsto_volume_inter_and_sdiff_ball_of_indicator_tendsto hE_seq_meas
      hC_min.measurableSet (ht (closedBall 0 R) (isCompact_closedBall 0 R))
    have hc_pos : 0 < minimizerVolumeDensityConst m * R ^ (m + 1) :=
      mul_pos (minimizerVolumeDensityConst_pos m) (pow_pos hR (m + 1))
    have hge1 : minimizerVolumeDensityConst m * R ^ (m + 1) ≤ volume.real (C ∩ ball 0 R) :=
      ge_of_tendsto hvol_lim.1 (hev_vol.mono fun _ h ↦ h.1)
    have hge2 : minimizerVolumeDensityConst m * R ^ (m + 1) ≤ volume.real (ball 0 R \ C) :=
      ge_of_tendsto hvol_lim.2 (hev_vol.mono fun _ h ↦ h.2)
    refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
    · have : volume.real (C ∩ ball 0 R) = 0 := by simp [Measure.real, h0]
      linarith
    · have : volume.real (ball 0 R \ C) = 0 := by simp [Measure.real, h0]
      linarith
  have hvol_C : volume C ≠ 0 :=
    fun h0 ↦ (h0_bdry 1 zero_lt_one).1 (measure_mono_null inter_subset_left h0)
  have hvol_Cc : volume Cᶜ ≠ 0 :=
    fun h0 ↦ (h0_bdry 1 zero_lt_one).2
      (measure_mono_null (fun _ hy ↦ hy.2) h0)
  let hPC_int (n : ℕ) : variationalPerimeter b C (ball 0 ((n : ℝ) + 1)) ≠ ⊤ :=
    hC_min.perimeter_ball_ne_top 0 ((n : ℝ) + 1) (by positivity) (subset_univ _)
  let μC := perimeterRadonMeasure b hC_min.measurableSet hPC_int
  have hP_exact (R : ℝ) (hR : 0 < R) :
      (variationalPerimeter b C (ball 0 R)).toReal = perimeterDensity b E x₀ * R ^ m := by
    refine ball_perimeter_eq_theta_mul_pow_of_ae_sphere_zero hC_min μC (fun s hs hsph ↦ ?_) hR
    have hconv_enn := hP_sph 0 s hs μC inferInstance
      (fun U hU ↦ perimeterRadonMeasure_apply_open b hC_min.measurableSet hPC_int hU) hsph
    have hPC_s : variationalPerimeter b C (ball 0 s) ≠ ⊤ :=
      hC_min.perimeter_ball_ne_top 0 s hs (subset_univ _)
    have hconv_real := (ENNReal.tendsto_toReal hPC_s).comp hconv_enn
    have hscale_eq (j : ℕ) :
        (variationalPerimeter b (E_seq (φ j)) (ball 0 s)).toReal =
          ((r_seq (φ j) * s) ^ (-(m : ℤ)) *
            (variationalPerimeter b E (ball x₀ (r_seq (φ j) * s))).toReal) * s ^ m := by
      have hp := variationalPerimeter_preimage_add_smul_ball (d := m + 1) (by omega) b E x₀ 0
        (hr_pos (φ j)) (ρ := s)
      simp only [Nat.add_sub_cancel, smul_zero, add_zero] at hp
      change (variationalPerimeter b ((fun y ↦ x₀ + r_seq (φ j) • y) ⁻¹' E) (ball 0 s)).toReal = _
      rw [hp, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (hr_pos (φ j)).le m)),
        zpow_neg, zpow_natCast, mul_pow]
      have hsm_ne : s ^ m ≠ 0 := pow_ne_zero m hs.ne'
      have hrm_ne : (r_seq (φ j)) ^ m ≠ 0 := pow_ne_zero m (hr_pos (φ j)).ne'
      field_simp
    have hrs_nhds : Tendsto (fun j ↦ r_seq (φ j) * s) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun j ↦ mul_pos (hr_pos (φ j)) hs⟩
      change Tendsto (fun j ↦ (r_seq ∘ φ) j * s) atTop (𝓝 0)
      simpa only [zero_mul] using (hr_lim.comp hφ.tendsto_atTop).mul_const s
    have hrhs_lim : Tendsto
        (fun j ↦ ((r_seq (φ j) * s) ^ (-(m : ℤ)) *
          (variationalPerimeter b E (ball x₀ (r_seq (φ j) * s))).toReal) * s ^ m)
        atTop (𝓝 (perimeterDensity b E x₀ * s ^ m)) :=
      ((hmin.tendsto_perimeterDensity hx₀.2).comp hrs_nhds).mul_const (s ^ m)
    exact tendsto_nhds_unique hconv_real (hrhs_lim.congr fun j ↦ (hscale_eq j).symm)
  have hconst_C (R : ℝ) (hR : 0 < R) :
      R ^ (-(m : ℤ)) * (variationalPerimeter b C (ball 0 R)).toReal = perimeterDensity b E x₀ := by
    rw [hP_exact R hR, zpow_neg, zpow_natCast]
    have hne : R ^ m ≠ 0 := pow_ne_zero m hR.ne'
    field_simp
  exact ⟨φ, C, hφ, hC_min.measurableSet, hC_min, h0_bdry, hvol_C, hvol_Cc, ht, hP_exact,
    fun a ha ↦ hC_min.ae_mem_smul_iff_of_constant_perimeter_ratio hconst_C ha⟩

/-- Existence of nontrivial minimal blowdown cones centered at `x₀ ∈ measureTheoreticBoundary E`
(BV11): for any global perimeter minimizer `E` on `univ` and scale sequence `R_seq → ∞`, a
subsequence of `(E - x₀) / R_seq` converges in `L¹_loc` to a nontrivial global perimeter-minimizing
cone `C` with `P(C, ball 0 R) = perimeterInfinityDensity b E x₀ * R ^ m` for every `R > 0`. -/
theorem IsLocalPerimeterMinimizer.exists_blowdown_cone_at {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) {x₀ : Space (m + 1)}
    (hx₀ : x₀ ∈ measureTheoreticBoundary E)
    {R_seq : ℕ → ℝ} (hR_pos : ∀ j, 0 < R_seq j) (hR_lim : Tendsto R_seq atTop atTop) :
    ∃ (φ : ℕ → ℕ) (C : Set (Space (m + 1))),
      StrictMono φ ∧
      MeasurableSet C ∧
      IsLocalPerimeterMinimizer b C univ ∧
      (0 : Space (m + 1)) ∈ measureTheoreticBoundary C ∧
      volume C ≠ 0 ∧ volume Cᶜ ≠ 0 ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ y in K,
          ‖((fun z ↦ x₀ + R_seq (φ j) • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
            C.indicator (fun _ ↦ (1 : ℝ)) y‖)
          atTop (𝓝 0)) ∧
      (∀ R : ℝ, 0 < R →
        (variationalPerimeter b C (ball 0 R)).toReal =
          perimeterInfinityDensity b E x₀ * R ^ m) ∧
      (∀ a : ℝ, 0 < a → ∀ᵐ y ∂volume, y ∈ C ↔ a • y ∈ C) := by
  let E_seq : ℕ → Set (Space (m + 1)) := fun j ↦ (fun z ↦ x₀ + R_seq j • z) ⁻¹' E
  have hmin_all (j : ℕ) : IsLocalPerimeterMinimizer b (E_seq j) univ := by
    simpa [E_seq] using hmin.preimage_add_smul (by omega) x₀ (hR_pos j)
  obtain ⟨φ, C, hφ, hC_min, ht, -, hP_sph⟩ :=
    exists_subsequence_univ_isLocalPerimeterMinimizer (by omega) b E_seq hmin_all
  have hE_seq_meas (j : ℕ) : MeasurableSet (E_seq (φ j)) := (hmin_all (φ j)).measurableSet
  have h0_bdry : (0 : Space (m + 1)) ∈ measureTheoreticBoundary C := by
    intro R hR
    have hvol_j (j : ℕ) :
        minimizerVolumeDensityConst m * R ^ (m + 1) ≤ volume.real (E_seq (φ j) ∩ ball 0 R) ∧
          minimizerVolumeDensityConst m * R ^ (m + 1) ≤ volume.real (ball 0 R \ E_seq (φ j)) := by
      have h0_j : (0 : Space (m + 1)) ∈ measureTheoreticBoundary (E_seq (φ j)) := by
        rw [mem_measureTheoreticBoundary_preimage_add_smul E x₀ 0 (hR_pos (φ j))]
        simpa using hx₀
      exact ⟨(hmin_all (φ j)).volume_inter_ball_ge h0_j hR (subset_univ _),
        (hmin_all (φ j)).volume_sdiff_ball_ge h0_j hR (subset_univ _)⟩
    have hvol_lim := tendsto_volume_inter_and_sdiff_ball_of_indicator_tendsto hE_seq_meas
      hC_min.measurableSet (ht (closedBall 0 R) (isCompact_closedBall 0 R))
    have hc_pos : 0 < minimizerVolumeDensityConst m * R ^ (m + 1) :=
      mul_pos (minimizerVolumeDensityConst_pos m) (pow_pos hR (m + 1))
    have hge1 : minimizerVolumeDensityConst m * R ^ (m + 1) ≤ volume.real (C ∩ ball 0 R) :=
      ge_of_tendsto hvol_lim.1 (Eventually.of_forall fun j ↦ (hvol_j j).1)
    have hge2 : minimizerVolumeDensityConst m * R ^ (m + 1) ≤ volume.real (ball 0 R \ C) :=
      ge_of_tendsto hvol_lim.2 (Eventually.of_forall fun j ↦ (hvol_j j).2)
    refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
    · have : volume.real (C ∩ ball 0 R) = 0 := by simp [Measure.real, h0]
      linarith
    · have : volume.real (ball 0 R \ C) = 0 := by simp [Measure.real, h0]
      linarith
  have hvol_C : volume C ≠ 0 :=
    fun h0 ↦ (h0_bdry 1 zero_lt_one).1 (measure_mono_null inter_subset_left h0)
  have hvol_Cc : volume Cᶜ ≠ 0 :=
    fun h0 ↦ (h0_bdry 1 zero_lt_one).2 (measure_mono_null (fun _ hy ↦ hy.2) h0)
  let hPC_int (n : ℕ) : variationalPerimeter b C (ball 0 ((n : ℝ) + 1)) ≠ ⊤ :=
    hC_min.perimeter_ball_ne_top 0 ((n : ℝ) + 1) (by positivity) (subset_univ _)
  let μC := perimeterRadonMeasure b hC_min.measurableSet hPC_int
  have hP_exact (R : ℝ) (hR : 0 < R) :
      (variationalPerimeter b C (ball 0 R)).toReal =
        perimeterInfinityDensity b E x₀ * R ^ m := by
    refine ball_perimeter_eq_theta_mul_pow_of_ae_sphere_zero hC_min μC (fun s hs hsph ↦ ?_) hR
    have hconv_enn := hP_sph 0 s hs μC inferInstance
      (fun U hU ↦ perimeterRadonMeasure_apply_open b hC_min.measurableSet hPC_int hU) hsph
    have hPC_s : variationalPerimeter b C (ball 0 s) ≠ ⊤ :=
      hC_min.perimeter_ball_ne_top 0 s hs (subset_univ _)
    have hconv_real := (ENNReal.tendsto_toReal hPC_s).comp hconv_enn
    have hscale_eq (j : ℕ) :
        (variationalPerimeter b (E_seq (φ j)) (ball 0 s)).toReal =
          ((R_seq (φ j) * s) ^ (-(m : ℤ)) *
            (variationalPerimeter b E (ball x₀ (R_seq (φ j) * s))).toReal) * s ^ m := by
      have hp := variationalPerimeter_preimage_add_smul_ball (d := m + 1) (by omega) b E x₀ 0
        (hR_pos (φ j)) (ρ := s)
      simp only [Nat.add_sub_cancel, smul_zero, add_zero] at hp
      change (variationalPerimeter b ((fun y ↦ x₀ + R_seq (φ j) • y) ⁻¹' E) (ball 0 s)).toReal = _
      rw [hp, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (hR_pos (φ j)).le m)),
        zpow_neg, zpow_natCast, mul_pow]
      have hsm_ne : s ^ m ≠ 0 := pow_ne_zero m hs.ne'
      have hrm_ne : (R_seq (φ j)) ^ m ≠ 0 := pow_ne_zero m (hR_pos (φ j)).ne'
      field_simp
    have hRs_atTop : Tendsto (fun j ↦ R_seq (φ j) * s) atTop atTop :=
      (hR_lim.comp hφ.tendsto_atTop).atTop_mul_const hs
    have hrhs_lim : Tendsto
        (fun j ↦ ((R_seq (φ j) * s) ^ (-(m : ℤ)) *
          (variationalPerimeter b E (ball x₀ (R_seq (φ j) * s))).toReal) * s ^ m)
        atTop (𝓝 (perimeterInfinityDensity b E x₀ * s ^ m)) :=
      ((hmin.tendsto_perimeterInfinityDensity x₀).comp hRs_atTop).mul_const (s ^ m)
    exact tendsto_nhds_unique hconv_real (hrhs_lim.congr fun j ↦ (hscale_eq j).symm)
  have hconst_C (R : ℝ) (hR : 0 < R) :
      R ^ (-(m : ℤ)) * (variationalPerimeter b C (ball 0 R)).toReal =
        perimeterInfinityDensity b E x₀ := by
    rw [hP_exact R hR, zpow_neg, zpow_natCast]
    have hne : R ^ m ≠ 0 := pow_ne_zero m hR.ne'
    field_simp
  exact ⟨φ, C, hφ, hC_min.measurableSet, hC_min, h0_bdry, hvol_C, hvol_Cc, ht, hP_exact,
    fun a ha ↦ hC_min.ae_mem_smul_iff_of_constant_perimeter_ratio hconst_C ha⟩

/-- Origin-centered form of `IsLocalPerimeterMinimizer.exists_blowdown_cone_at` (BV11). -/
theorem IsLocalPerimeterMinimizer.exists_blowdown_cone {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ)
    (h0 : (0 : Space (m + 1)) ∈ measureTheoreticBoundary E)
    {R_seq : ℕ → ℝ} (hR_pos : ∀ j, 0 < R_seq j) (hR_lim : Tendsto R_seq atTop atTop) :
    ∃ (φ : ℕ → ℕ) (C : Set (Space (m + 1))),
      StrictMono φ ∧
      MeasurableSet C ∧
      IsLocalPerimeterMinimizer b C univ ∧
      (0 : Space (m + 1)) ∈ measureTheoreticBoundary C ∧
      volume C ≠ 0 ∧ volume Cᶜ ≠ 0 ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ y in K,
          ‖((fun z ↦ R_seq (φ j) • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
            C.indicator (fun _ ↦ (1 : ℝ)) y‖)
          atTop (𝓝 0)) ∧
      (∀ R : ℝ, 0 < R →
        (variationalPerimeter b C (ball 0 R)).toReal =
          perimeterInfinityDensity b E 0 * R ^ m) ∧
      (∀ a : ℝ, 0 < a → ∀ᵐ y ∂volume, y ∈ C ↔ a • y ∈ C) := by
  simpa only [zero_add] using hmin.exists_blowdown_cone_at h0 hR_pos hR_lim

end SerrinEpigraph
