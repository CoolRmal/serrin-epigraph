module

public import SerrinEpigraph.LocalPerimeterMinimizer
public import SerrinEpigraph.PerimeterRadonRepresentation
public import SerrinEpigraph.MinimizerDensity
public import SerrinEpigraph.MinimizerCompactness
public import SerrinEpigraph.PlaneTiltPerimeter
public import SerrinEpigraph.MeasurablePhaseMollification
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Covering.Differentiation

/-!
# Perimeter-almost-everywhere halfspace tangents and unit perimeter density (BV12)

For local perimeter minimizers (`IsLocalPerimeterMinimizer b E Ω`) in `Space (m + 1)` (`m : ℕ`),
this module proves BV12 of `docs/rigidity-proof/bv-minimizers.md` without presupposing De Giorgi
rectifiability:
- **Besicovitch polar vector differentiation (BV12.1)**: for any locally finite measure `μ`,
  open set `Ω₀`, and unit polar field `ν` integrable on `μ.restrict Ω₀`, for `(μ.restrict Ω₀)`-a.e.
  `x₀` we have `x₀ ∈ Ω₀`, `x₀ ∈ Measure.support μ`, `‖ν x₀‖ = 1`, and the closed-ball polar
  oscillation average `(μ.real (closedBall x₀ r))⁻¹ * ∫ y in closedBall x₀ r, ‖ν y - ν x₀‖ ∂μ`
  converges to `0` as `r → 0+`.
- **Smooth-mollification halfspace identification (BV12.2–BV12.3)**: any measurable phase `C` with
  `0 ∈ measureTheoreticBoundary C` whose distributional directional derivatives vanish in every
  direction orthogonal to a unit vector `e` and are nonnegative in direction `e` coincides almost
  everywhere with the open halfspace `{y | 0 < inner ℝ e y}`.
- **Deterministic pointwise tangent halfspace and unit perimeter density criterion
  (BV12.2–BV12.4)**: at *any* single point `x₀ ∈ measureTheoreticBoundary E ∩ Ω₀` where the closed
  ball polar oscillation around a unit vector `e` tends to `0`, the blowups
  `(fun z ↦ x₀ + r • z) ⁻¹' E` converge in `L¹_loc` along the *full* filter `r → 0+` to
  `{y | 0 < inner ℝ e y}`, and the normalized ball perimeters
  `r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal`,
  `r ^ (-(m : ℤ)) * μ.real (ball x₀ r)`, and `r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r)` all
  converge to `volume.real (closedBall (0 : Space m) 1)` as `r → 0+`.
- **Local and global a.e. halfspace tangent theorems**: combining Besicovitch differentiation with
  the deterministic pointwise criterion yields halfspace tangents and unit perimeter density
  `(μ.restrict Ω₀)`-a.e. on local polar charts, `(μ.restrict Ω)`-a.e. on any open domain `Ω`, and
  `μ`-a.e. globally on `univ` (including for `perimeterRadonMeasure`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter ContinuousLinearMap
open scoped Topology CompactlySupported ENNReal Convolution

namespace SerrinEpigraph

/-! ### 1. Besicovitch differentiation of the polar vector field (BV12.1) -/

/-- Besicovitch closed-ball differentiation for a unit polar vector field `ν` on an open set `Ω₀`
with respect to a locally finite measure `μ` (BV12.1). -/
theorem ae_polar_besicovitch_differentiation {d : ℕ}
    (μ : Measure (Space d)) [IsLocallyFiniteMeasure μ]
    {Ω₀ : Set (Space d)} (hΩ₀ : IsOpen Ω₀)
    {ν : Space d → Space d} (hν_int : Integrable ν (μ.restrict Ω₀))
    (hν_norm : ∀ᵐ x ∂μ.restrict Ω₀, ‖ν x‖ = 1) :
    ∀ᵐ x₀ ∂μ.restrict Ω₀,
      x₀ ∈ Ω₀ ∧ x₀ ∈ Measure.support μ ∧ ‖ν x₀‖ = 1 ∧
      Tendsto (fun r ↦ ⨍ y in closedBall x₀ r, ‖ν y - ν x₀‖ ∂μ) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r ↦ (μ.real (closedBall x₀ r))⁻¹ *
        ∫ y in closedBall x₀ r, ‖ν y - ν x₀‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
  let μ₀ := μ.restrict Ω₀
  have hdiff := (Besicovitch.vitaliFamily μ₀).ae_tendsto_average_norm_sub hν_int.locallyIntegrable
  have hmem : ∀ᵐ x₀ ∂μ₀, x₀ ∈ Ω₀ := ae_restrict_mem hΩ₀.measurableSet
  have hsupp : ∀ᵐ x₀ ∂μ₀, x₀ ∈ Measure.support μ :=
    ae_restrict_of_ae (ae_iff.mpr Measure.measure_compl_support)
  filter_upwards [hmem, hsupp, hν_norm, hdiff] with x₀ hx₀ hx₀_supp hν_x₀ hx₀_diff
  obtain ⟨r₀, hr₀, hcb₀⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ₀.mem_nhds hx₀)
  have hfilter := hx₀_diff.comp (Besicovitch.tendsto_filterAt μ₀ x₀)
  have havg : Tendsto (fun r ↦ ⨍ y in closedBall x₀ r, ‖ν y - ν x₀‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
    refine hfilter.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT hr₀] with r hr
    have hsub : closedBall x₀ r ⊆ Ω₀ := (closedBall_subset_closedBall hr.2).trans hcb₀
    have hres_meas : μ₀.real (closedBall x₀ r) = μ.real (closedBall x₀ r) := by
      simp [μ₀, Measure.real, Measure.restrict_apply measurableSet_closedBall,
        inter_eq_left.mpr hsub]
    have hres_int : (∫ y in closedBall x₀ r, ‖ν y - ν x₀‖ ∂μ₀) =
        ∫ y in closedBall x₀ r, ‖ν y - ν x₀‖ ∂μ := by
      dsimp [μ₀]
      rw [Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.mpr hsub]
    simp only [Function.comp_def, setAverage_eq, hres_meas, hres_int]
  have hmul : Tendsto (fun r ↦ (μ.real (closedBall x₀ r))⁻¹ *
      ∫ y in closedBall x₀ r, ‖ν y - ν x₀‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
    refine havg.congr fun r ↦ ?_
    rw [setAverage_eq, smul_eq_mul]
  exact ⟨hx₀, hx₀_supp, hν_x₀, havg, hmul⟩

/-! ### 2. Halfspace identification from weak directional derivatives (BV12.2–BV12.3) -/

set_option backward.isDefEq.respectTransparency false in
/-- Directional derivative of a smooth mollification expressed against reflected kernel tests. -/
theorem fderiv_mollify_eq_neg_integral {d : ℕ} {u : Space d → ℝ}
    (hu : LocallyIntegrable u volume) (n : ℕ) (y v : Space d) :
    fderiv ℝ (mollify u n) y v =
      -(∫ z, u z * fderiv ℝ (fun w ↦ (averagingBump d n).normed volume (y - w)) z v) := by
  let k : Space d → ℝ := (averagingBump d n).normed volume
  have hck : HasCompactSupport k := (averagingBump d n).hasCompactSupport_normed
  have hk : ContDiff ℝ 1 k := (averagingBump d n).contDiff_normed
  have hmoll : mollify u n = u ⋆[(lsmul ℝ ℝ).flip, volume] k := by
    dsimp [mollify, k]
    rw [← MeasureTheory.convolution_flip]
  have hfd := (hck.hasFDerivAt_convolution_right (lsmul ℝ ℝ).flip hu hk y).fderiv
  rw [hmoll, hfd,
    MeasureTheory.convolution_precompR_apply (lsmul ℝ ℝ).flip hu (hck.fderiv ℝ)
      (hk.continuous_fderiv one_ne_zero) y v]
  change (∫ z, fderiv ℝ k (y - z) v * u z) =
    -(∫ z, u z * fderiv ℝ (fun w ↦ k (y - w)) z v)
  rw [← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
  dsimp only
  have hsub_fd : HasFDerivAt (fun w : Space d ↦ y - w) (-ContinuousLinearMap.id ℝ (Space d)) z := by
    convert (hasFDerivAt_const y z).sub (hasFDerivAt_id z) using 1
    · rfl
    · exact (zero_sub _).symm
  have hcomp_fd : HasFDerivAt (fun w : Space d ↦ k (y - w))
      ((fderiv ℝ k (y - z)).comp (-ContinuousLinearMap.id ℝ (Space d))) z :=
    (hk.differentiable one_ne_zero (y - z)).hasFDerivAt.comp z hsub_fd
  have hval : fderiv ℝ (fun w : Space d ↦ k (y - w)) z v = -(fderiv ℝ k (y - z) v) := by
    rw [hcomp_fd.fderiv]
    simp
  rw [hval]
  ring

/-- Every hyperplane orthogonal to a nonzero vector in `Space d` has Lebesgue measure zero. -/
theorem volume_orthogonal_hyperplane_eq_zero {d : ℕ} {e : Space d} (he : e ≠ 0) :
    volume {y : Space d | inner ℝ e y = 0} = 0 := by
  let K : Submodule ℝ (Space d) := LinearMap.ker (innerSL ℝ e).toLinearMap
  have hK_ne : K ≠ ⊤ := by
    intro htop
    have heK : e ∈ K := htop ▸ Submodule.mem_top
    have h0 : inner ℝ e e = 0 := heK
    exact he (inner_self_eq_zero.mp h0)
  have hset : {y : Space d | inner ℝ e y = 0} = (K : Set (Space d)) := rfl
  rw [hset]
  exact Measure.addHaar_submodule volume K hK_ne

/-- Direct mollification identification of a halfspace (BV12.2–BV12.3): if `C` is measurable with
`0 ∈ measureTheoreticBoundary C`, every orthogonal distributional derivative of `1_C` vanishes, and
the distributional derivative along the unit vector `e` is nonnegative, then
`C =ᵐ[volume] {y | 0 < inner ℝ e y}`. -/
theorem ae_eq_positive_halfspace_of_weak_directional_deriv {d : ℕ}
    {C : Set (Space d)} (hC : MeasurableSet C) (h0 : 0 ∈ measureTheoreticBoundary C)
    {e : Space d} (he : ‖e‖ = 1)
    (horth : ∀ ψ : Space d → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      ∀ v : Space d, inner ℝ e v = 0 →
        (∫ y, C.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v) = 0)
    (hmono : ∀ ψ : Space d → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∀ y, 0 ≤ ψ y) →
        0 ≤ -(∫ y, C.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y e)) :
    C =ᵐ[volume] {y : Space d | 0 < inner ℝ e y} := by
  let u : Space d → ℝ := C.indicator (fun _ ↦ (1 : ℝ))
  have hu_loc : LocallyIntegrable u volume := locallyIntegrable_phaseIndicator hC
  have hψ_smooth (n : ℕ) (y : Space d) :
      ContDiff ℝ 1 (fun w ↦ (averagingBump d n).normed volume (y - w)) :=
    ((averagingBump d n).contDiff_normed (n := 1)).comp (contDiff_const.sub contDiff_id)
  have hψ_comp (n : ℕ) (y : Space d) :
      HasCompactSupport (fun w ↦ (averagingBump d n).normed volume (y - w)) := by
    let k := (averagingBump d n).normed volume
    have hck : HasCompactSupport k := (averagingBump d n).hasCompactSupport_normed
    have himg : IsCompact ((fun w : Space d ↦ y - w) '' tsupport k) :=
      hck.image (continuous_const.sub continuous_id)
    refine himg.of_isClosed_subset (isClosed_tsupport _) ?_
    refine (tsupport_comp_subset_preimage k (continuous_const.sub continuous_id)).trans ?_
    intro w hw
    exact ⟨y - w, hw, sub_sub_cancel y w⟩
  have hmoll_orth (n : ℕ) (y v : Space d) (hv : inner ℝ e v = 0) :
      fderiv ℝ (mollify u n) y v = 0 := by
    rw [fderiv_mollify_eq_neg_integral hu_loc n y v,
      horth _ (hψ_smooth n y) (hψ_comp n y) v hv, neg_zero]
  have hmoll_profile (n : ℕ) (x : Space d) :
      mollify u n x = mollify u n ((inner ℝ e x) • e) := by
    let ξ : Space d := x - (inner ℝ e x) • e
    have hξ : inner ℝ e ξ = 0 := by
      simp [ξ, inner_sub_right, inner_smul_right, he]
    have hm_cd := mollify_contDiff_of_locallyIntegrable hu_loc n
    have hd (t : ℝ) :
        HasDerivAt (fun s : ℝ ↦ mollify u n ((inner ℝ e x) • e + s • ξ)) 0 t := by
      have hh := (hm_cd.differentiable (by simp)
        ((inner ℝ e x) • e + t • ξ)).hasFDerivAt.comp_hasDerivAt t
          (((hasDerivAt_id t).smul_const ξ).const_add ((inner ℝ e x) • e))
      convert hh using 1
      · rfl
      · simpa only [one_smul] using (hmoll_orth n ((inner ℝ e x) • e + t • ξ) ξ hξ).symm
    have hconst := is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt)
      (fun t ↦ (hd t).deriv) (1 : ℝ) 0
    simpa only [ξ, one_smul, zero_smul, add_zero, add_sub_cancel] using hconst
  let f : ℕ → ℝ → ℝ := fun n t ↦ mollify u n (t • e)
  have hf_mono (n : ℕ) : Monotone (f n) := by
    have hm_cd := mollify_contDiff_of_locallyIntegrable hu_loc n
    have hfd (t : ℝ) : HasDerivAt (f n) (fderiv ℝ (mollify u n) (t • e) e) t := by
      have hh := (hm_cd.differentiable (by simp) (t • e)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const e)
      convert hh using 1
      · rfl
      · simp
    refine monotone_of_deriv_nonneg (fun t ↦ (hfd t).differentiableAt) fun t ↦ ?_
    rw [(hfd t).deriv, fderiv_mollify_eq_neg_integral hu_loc n (t • e) e]
    exact hmono _ (hψ_smooth n (t • e)) (hψ_comp n (t • e))
      fun w ↦ (averagingBump d n).nonneg_normed (t • e - w)
  let G : Set (Space d) := {y | Tendsto (fun n ↦ mollify u n y) atTop (𝓝 (u y))}
  have hG_ae : ∀ᵐ y ∂volume, y ∈ G := mollify_tendsto_ae_of_locallyIntegrable hu_loc
  have hG_compl : volume Gᶜ = 0 := ae_iff.mp hG_ae
  have hu_order {x₁ x₂ : Space d} (hx₁ : x₁ ∈ G) (hx₂ : x₂ ∈ G)
      (hle : inner ℝ e x₁ ≤ inner ℝ e x₂) : u x₁ ≤ u x₂ := by
    refine le_of_tendsto_of_tendsto hx₁ hx₂ (Eventually.of_forall fun n ↦ ?_)
    dsimp only
    rw [hmoll_profile n x₁, hmoll_profile n x₂]
    exact hf_mono n hle
  have hpos_mem {x : Space d} (hxG : x ∈ G) (hpos : 0 < inner ℝ e x) : x ∈ C := by
    let ε : ℝ := inner ℝ e x
    have hne0 : volume ((C ∩ ball 0 ε) ∩ G) ≠ 0 := by
      intro hzero
      have hcov : C ∩ ball 0 ε ⊆ ((C ∩ ball 0 ε) ∩ G) ∪ Gᶜ := by
        intro z hz
        by_cases hzG : z ∈ G
        · exact Or.inl ⟨hz, hzG⟩
        · exact Or.inr hzG
      have hle0 : volume (C ∩ ball 0 ε) ≤ 0 := by
        calc
          volume (C ∩ ball 0 ε) ≤ volume (((C ∩ ball 0 ε) ∩ G) ∪ Gᶜ) := measure_mono hcov
          _ ≤ volume ((C ∩ ball 0 ε) ∩ G) + volume Gᶜ := measure_union_le _ _
          _ = 0 := by rw [hzero, hG_compl, add_zero]
      exact (h0 ε hpos).1 (nonpos_iff_eq_zero.mp hle0)
    obtain ⟨z, ⟨hzC, hzb⟩, hzG⟩ := nonempty_of_measure_ne_zero hne0
    have hz_norm : ‖z‖ < ε := by simpa [mem_ball, dist_zero_right] using hzb
    have hz_le : inner ℝ e z ≤ inner ℝ e x := by
      calc
        inner ℝ e z ≤ ‖e‖ * ‖z‖ := real_inner_le_norm e z
        _ = ‖z‖ := by rw [he, one_mul]
        _ ≤ inner ℝ e x := hz_norm.le
    have h1 : (1 : ℝ) ≤ u x := by
      have hle := hu_order hzG hxG hz_le
      simpa [u, hzC] using hle
    by_contra hxC
    simp [u, hxC] at h1
    linarith
  have hneg_notMem {x : Space d} (hxG : x ∈ G) (hneg : inner ℝ e x < 0) : x ∉ C := by
    let ε : ℝ := -inner ℝ e x
    have hε : 0 < ε := neg_pos.mpr hneg
    have hne0 : volume ((ball 0 ε \ C) ∩ G) ≠ 0 := by
      intro hzero
      have hcov : ball 0 ε \ C ⊆ ((ball 0 ε \ C) ∩ G) ∪ Gᶜ := by
        intro z hz
        by_cases hzG : z ∈ G
        · exact Or.inl ⟨hz, hzG⟩
        · exact Or.inr hzG
      have hle0 : volume (ball 0 ε \ C) ≤ 0 := by
        calc
          volume (ball 0 ε \ C) ≤ volume (((ball 0 ε \ C) ∩ G) ∪ Gᶜ) := measure_mono hcov
          _ ≤ volume ((ball 0 ε \ C) ∩ G) + volume Gᶜ := measure_union_le _ _
          _ = 0 := by rw [hzero, hG_compl, add_zero]
      exact (h0 ε hε).2 (nonpos_iff_eq_zero.mp hle0)
    obtain ⟨z, ⟨hzb, hzC⟩, hzG⟩ := nonempty_of_measure_ne_zero hne0
    have hz_norm : ‖z‖ < ε := by simpa [mem_ball, dist_zero_right] using hzb
    have hz_ge : inner ℝ e x ≤ inner ℝ e z := by
      have hneg_z : -inner ℝ e z ≤ ‖z‖ := by
        calc
          -inner ℝ e z = inner ℝ e (-z) := (inner_neg_right e z).symm
          _ ≤ ‖e‖ * ‖-z‖ := real_inner_le_norm e (-z)
          _ = ‖z‖ := by rw [he, one_mul, norm_neg]
      have hlt : -inner ℝ e z < -inner ℝ e x := hneg_z.trans_lt hz_norm
      linarith
    have h0_ge : u x ≤ 0 := by
      have hle := hu_order hxG hzG hz_ge
      simpa [u, hzC] using hle
    intro hxC
    simp [u, hxC] at h0_ge
    linarith
  have he_ne : e ≠ 0 := by
    intro hzero
    simp [hzero] at he
  have hnot_zero : ∀ᵐ y ∂volume, inner ℝ e y ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using volume_orthogonal_hyperplane_eq_zero he_ne
  filter_upwards [hG_ae, hnot_zero] with x hxG hx_ne
  apply propext
  rcases lt_trichotomy 0 (inner ℝ e x) with hpos | heq | hneg
  · exact ⟨fun _ ↦ hpos, fun _ ↦ hpos_mem hxG hpos⟩
  · exact (hx_ne heq.symm).elim
  · exact ⟨fun hxC ↦ (hneg_notMem hxG hneg hxC).elim, fun hp ↦ (not_lt_of_gt hneg hp).elim⟩

/-! ### 3. Pointwise tangent halfspace and unit perimeter density criterion (BV12.2–BV12.4) -/

/-- General subsequential contradiction upgrade along `𝓝[>] 0`: if every positive null sequence has
a subsequence along which `F` tends to `L`, then `Tendsto F (𝓝[>] 0) (𝓝 L)`. -/
private theorem tendsto_nhdsGT_zero_of_subseq {X : Type*} [PseudoMetricSpace X]
    {F : ℝ → X} {L : X}
    (hsub : ∀ r_seq : ℕ → ℝ, (∀ j, 0 < r_seq j) → Tendsto r_seq atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k ↦ F (r_seq (φ k))) atTop (𝓝 L)) :
    Tendsto F (𝓝[>] 0) (𝓝 L) := by
  by_contra hnot
  rw [Metric.tendsto_nhdsWithin_nhds] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hbad⟩ := hnot
  have hex (j : ℕ) : ∃ r : ℝ, 0 < r ∧ r < 1 / ((j : ℝ) + 1) ∧ ε ≤ dist (F r) L := by
    obtain ⟨r, hr_mem, hr_dist, hr_ge⟩ := hbad (1 / ((j : ℝ) + 1)) (by positivity)
    have hr_pos : 0 < r := hr_mem
    have hr_lt : r < 1 / ((j : ℝ) + 1) := by
      simpa [Real.dist_eq, abs_of_pos hr_pos] using hr_dist
    exact ⟨r, hr_pos, hr_lt, hr_ge⟩
  choose r_seq hr_pos hr_lt hr_ge using hex
  have hr_lim : Tendsto r_seq atTop (𝓝 0) :=
    squeeze_zero (fun j ↦ (hr_pos j).le) (fun j ↦ (hr_lt j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, -, hF_lim⟩ := hsub r_seq hr_pos hr_lim
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hF_lim ε hε
  exact not_lt_of_ge (hr_ge (φ N)) (hN N le_rfl)

/-- Rescaled directional distributional identity and vanishing polar oscillation error at `x₀`
as `r → 0+`. -/
private theorem rescaled_directional_pairing_decomposition {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω Ω₀ : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (hΩ₀ : IsOpen Ω₀) (hΩ₀_sub : Ω₀ ⊆ Ω)
    (μ : Measure (Space (m + 1))) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ Ω₀ → μ U = variationalPerimeter b E U)
    {ν : Space (m + 1) → Space (m + 1)} (hν_int : Integrable ν (μ.restrict Ω₀))
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ Ω₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω₀)
    {x₀ e : Space (m + 1)} (hx₀_Ω₀ : x₀ ∈ Ω₀)
    (hosc : Tendsto (fun r ↦ (μ.real (closedBall x₀ r))⁻¹ *
      ∫ y in closedBall x₀ r, ‖ν y - e‖ ∂μ) (𝓝[>] 0) (𝓝 0))
    {ψ : Space (m + 1) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ)
    (v : Space (m + 1)) :
    ∃ (R : ℝ) (err : ℝ → ℝ), 0 < R ∧ Tendsto err (𝓝[>] 0) (𝓝 0) ∧
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        -(∫ y, ((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v) =
          inner ℝ v e *
            ((r ^ m)⁻¹ * ∫ x in closedBall x₀ (r * R), ψ (r⁻¹ • (x - x₀)) ∂μ) + err r := by
  obtain ⟨N, hN⟩ := compact_subset_perimeter_ball hcψ
  let R : ℝ := (N : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let err : ℝ → ℝ := fun r ↦
    (r ^ m)⁻¹ * ∫ x in closedBall x₀ (r * R), ψ (r⁻¹ • (x - x₀)) * inner ℝ v (ν x - e) ∂μ
  obtain ⟨δ₀, hδ₀, hcb₀⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ₀.mem_nhds hx₀_Ω₀)
  have hmin₀ : IsLocalPerimeterMinimizer b E Ω₀ := hmin.mono hΩ₀ hΩ₀_sub
  obtain ⟨M₀, hM₀⟩ := hcψ.exists_bound_of_continuous hψ.continuous
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hψ_le (y : Space (m + 1)) : ‖ψ y‖ ≤ M := (hM₀ y).trans (le_max_left M₀ 0)
  have herr_tendsto : Tendsto err (𝓝[>] 0) (𝓝 0) := by
    have hmulR : Tendsto (fun r : ℝ ↦ r * R) (𝓝[>] 0) (𝓝[>] 0) := by
      have h0 : Tendsto (fun r : ℝ ↦ r * R) (𝓝 0) (𝓝 (0 * R)) :=
        (continuous_id.mul (continuous_const (y := R))).tendsto 0
      rw [zero_mul] at h0
      exact tendsto_nhdsWithin_iff.mpr
        ⟨h0.mono_left nhdsWithin_le_nhds, by
          filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
          exact mul_pos hr hR⟩
    have hosc_R : Tendsto (fun r : ℝ ↦ (μ.real (closedBall x₀ (r * R)))⁻¹ *
        ∫ y in closedBall x₀ (r * R), ‖ν y - e‖ ∂μ) (𝓝[>] 0) (𝓝 0) :=
      (hosc.comp hmulR).congr fun _ ↦ rfl
    let C_bound : ℝ := M * ‖v‖ * (minimizerPerimeterUpperConst m * R ^ m)
    have hupper_lim : Tendsto
        (fun r : ℝ ↦ C_bound * ((μ.real (closedBall x₀ (r * R)))⁻¹ *
          ∫ y in closedBall x₀ (r * R), ‖ν y - e‖ ∂μ))
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using hosc_R.const_mul C_bound
    refine squeeze_zero_norm' ?_ hupper_lim
    filter_upwards [Ioc_mem_nhdsGT (div_pos hδ₀ hR)] with r hr
    have hr_pos : 0 < r := hr.1
    have hrR_pos : 0 < r * R := mul_pos hr_pos hR
    have hrR_le : r * R ≤ δ₀ := (le_div_iff₀ hR).mp hr.2
    let B_r := closedBall x₀ (r * R)
    have hBr_Ω₀ : B_r ⊆ Ω₀ := (closedBall_subset_closedBall hrR_le).trans hcb₀
    have hBr_fin : μ B_r < ⊤ := (isCompact_closedBall x₀ (r * R)).measure_lt_top
    let _ : IsFiniteMeasure (μ.restrict B_r) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hBr_fin⟩
    have hν_Br : IntegrableOn ν B_r μ :=
      (show IntegrableOn ν Ω₀ μ from hν_int).mono_set hBr_Ω₀
    have hnorm_int : IntegrableOn (fun x ↦ ‖ν x - e‖) B_r μ :=
      (hν_Br.sub (integrableOn_const hBr_fin.ne)).norm
    have hpt (x : Space (m + 1)) :
        ‖ψ (r⁻¹ • (x - x₀)) * inner ℝ v (ν x - e)‖ ≤ (M * ‖v‖) * ‖ν x - e‖ := by
      rw [norm_mul]
      calc
        ‖ψ (r⁻¹ • (x - x₀))‖ * ‖inner ℝ v (ν x - e)‖ ≤
            M * (‖v‖ * ‖ν x - e‖) :=
          mul_le_mul (hψ_le _) (norm_inner_le_norm v (ν x - e)) (norm_nonneg _) hM_nonneg
        _ = (M * ‖v‖) * ‖ν x - e‖ := by ring
    have hint_le : ‖∫ x in B_r, ψ (r⁻¹ • (x - x₀)) * inner ℝ v (ν x - e) ∂μ‖ ≤
        (M * ‖v‖) * ∫ x in B_r, ‖ν x - e‖ ∂μ := by
      calc
        ‖∫ x in B_r, ψ (r⁻¹ • (x - x₀)) * inner ℝ v (ν x - e) ∂μ‖ ≤
            ∫ x in B_r, ‖ψ (r⁻¹ • (x - x₀)) * inner ℝ v (ν x - e)‖ ∂μ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ x in B_r, (M * ‖v‖) * ‖ν x - e‖ ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (hnorm_int.const_mul _) (Eventually.of_forall hpt)
        _ = (M * ‖v‖) * ∫ x in B_r, ‖ν x - e‖ ∂μ := integral_const_mul _ _
    have hmeas_scale : (r ^ m)⁻¹ * ∫ x in B_r, ‖ν x - e‖ ∂μ ≤
        (minimizerPerimeterUpperConst m * R ^ m) *
          ((μ.real B_r)⁻¹ * ∫ x in B_r, ‖ν x - e‖ ∂μ) := by
      rcases eq_or_ne (μ B_r) 0 with hμ0 | hμ_ne0
      · have hres0 : μ.restrict B_r = 0 := Measure.restrict_eq_zero.mpr hμ0
        simp [B_r, Measure.real, hμ0, hres0]
      · have hreal_pos : 0 < μ.real B_r := ENNReal.toReal_pos hμ_ne0 hBr_fin.ne
        have hcb_le := hmin₀.measure_closedBall_le μ hμ hrR_pos hBr_Ω₀
        have hnonneg_upper : 0 ≤ minimizerPerimeterUpperConst m * (r * R) ^ m :=
          mul_nonneg (minimizerPerimeterUpperConst_pos m).le (pow_nonneg hrR_pos.le _)
        have hreal_le : μ.real B_r ≤ minimizerPerimeterUpperConst m * (r * R) ^ m :=
          ENNReal.toReal_le_of_le_ofReal hnonneg_upper hcb_le
        have hratio_le : (r ^ m)⁻¹ * μ.real B_r ≤ minimizerPerimeterUpperConst m * R ^ m := by
          calc
            (r ^ m)⁻¹ * μ.real B_r ≤
                (r ^ m)⁻¹ * (minimizerPerimeterUpperConst m * (r * R) ^ m) :=
              mul_le_mul_of_nonneg_left hreal_le (inv_nonneg.mpr (pow_nonneg hr_pos.le m))
            _ = minimizerPerimeterUpperConst m * R ^ m := by
              rw [mul_pow]
              have hrm_ne : r ^ m ≠ 0 := (pow_pos hr_pos m).ne'
              field_simp
        have hint_nonneg : 0 ≤ (μ.real B_r)⁻¹ * ∫ x in B_r, ‖ν x - e‖ ∂μ :=
          mul_nonneg (inv_nonneg.mpr hreal_pos.le) (integral_nonneg fun _ ↦ norm_nonneg _)
        calc
          (r ^ m)⁻¹ * ∫ x in B_r, ‖ν x - e‖ ∂μ =
              ((r ^ m)⁻¹ * μ.real B_r) * ((μ.real B_r)⁻¹ * ∫ x in B_r, ‖ν x - e‖ ∂μ) := by
            have hne : μ.real B_r ≠ 0 := hreal_pos.ne'
            field_simp
          _ ≤ (minimizerPerimeterUpperConst m * R ^ m) *
              ((μ.real B_r)⁻¹ * ∫ x in B_r, ‖ν x - e‖ ∂μ) :=
            mul_le_mul_of_nonneg_right hratio_le hint_nonneg
    change ‖(r ^ m)⁻¹ * ∫ x in B_r, ψ (r⁻¹ • (x - x₀)) * inner ℝ v (ν x - e) ∂μ‖ ≤
      C_bound * ((μ.real B_r)⁻¹ * ∫ y in B_r, ‖ν y - e‖ ∂μ)
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hr_pos.le m))]
    calc
      (r ^ m)⁻¹ * ‖∫ x in B_r, ψ (r⁻¹ • (x - x₀)) * inner ℝ v (ν x - e) ∂μ‖ ≤
          (r ^ m)⁻¹ * ((M * ‖v‖) * ∫ x in B_r, ‖ν x - e‖ ∂μ) :=
        mul_le_mul_of_nonneg_left hint_le (inv_nonneg.mpr (pow_nonneg hr_pos.le m))
      _ = (M * ‖v‖) * ((r ^ m)⁻¹ * ∫ x in B_r, ‖ν x - e‖ ∂μ) := by ring
      _ ≤ (M * ‖v‖) * ((minimizerPerimeterUpperConst m * R ^ m) *
          ((μ.real B_r)⁻¹ * ∫ x in B_r, ‖ν x - e‖ ∂μ)) :=
        mul_le_mul_of_nonneg_left hmeas_scale (mul_nonneg hM_nonneg (norm_nonneg v))
      _ = C_bound * ((μ.real B_r)⁻¹ * ∫ y in B_r, ‖ν y - e‖ ∂μ) := by dsimp [C_bound]; ring
  refine ⟨R, err, hR, herr_tendsto, ?_⟩
  filter_upwards [Ioc_mem_nhdsGT (div_pos hδ₀ hR)] with r hr
  have hr_pos : 0 < r := hr.1
  have hrR_le : r * R ≤ δ₀ := (le_div_iff₀ hR).mp hr.2
  let B_r := closedBall x₀ (r * R)
  have hBr_Ω₀ : B_r ⊆ Ω₀ := (closedBall_subset_closedBall hrR_le).trans hcb₀
  let T : Space (m + 1) → Space (m + 1) := fun y ↦ x₀ + r • y
  let S : Space (m + 1) → Space (m + 1) := fun x ↦ r⁻¹ • (x - x₀)
  let G : Space (m + 1) → Space (m + 1) := fun y ↦ ψ y • v
  let f_r : Space (m + 1) → Space (m + 1) := fun x ↦ G (S x)
  have hS_cd : ContDiff ℝ 1 S := by fun_prop
  have hG_cd : ContDiff ℝ 1 G := hψ.smul contDiff_const
  have hfr_cd : ContDiff ℝ 1 f_r := hG_cd.comp hS_cd
  have hST (y : Space (m + 1)) : S (T y) = y := by simp [T, S, hr_pos.ne']
  have hts_fr : tsupport f_r ⊆ ball x₀ (r * R) := by
    have h1 : tsupport f_r ⊆ S ⁻¹' tsupport G :=
      tsupport_comp_subset_preimage G hS_cd.continuous
    have h2 : tsupport G ⊆ ball 0 R :=
      (tsupport_smul_subset_left ψ (fun _ ↦ v)).trans hN
    intro x hx
    have hxS : S x ∈ ball 0 R := h2 (h1 hx)
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr_pos.le)] at hxS
    rw [mem_ball, dist_eq_norm]
    exact (inv_mul_lt_iff₀ hr_pos).mp hxS
  have hc_fr : HasCompactSupport f_r :=
    (isCompact_closedBall x₀ (r * R)).of_isClosed_subset (isClosed_tsupport f_r)
      (hts_fr.trans ball_subset_closedBall)
  let F_r : C_c(Space (m + 1), Space (m + 1)) := ⟨⟨f_r, hfr_cd.continuous⟩, hc_fr⟩
  have hpair := hdist F_r hfr_cd (hts_fr.trans (ball_subset_closedBall.trans hBr_Ω₀))
  have hdiv_comp (y : Space (m + 1)) :
      fieldDivergence b f_r (T y) = r⁻¹ * fderiv ℝ ψ y v := by
    have hS_fd : HasFDerivAt S (r⁻¹ • ContinuousLinearMap.id ℝ (Space (m + 1))) (T y) :=
      ((hasFDerivAt_id (T y)).sub_const x₀).const_smul r⁻¹
    have hG_fd : HasFDerivAt G (fderiv ℝ G y) (S (T y)) := by
      rw [hST]
      exact (hG_cd.differentiable one_ne_zero y).hasFDerivAt
    have hcomp := (hG_fd.comp (T y) hS_fd).fderiv
    have hdivG : fieldDivergence b G y = fderiv ℝ ψ y v :=
      fieldDivergence_smul_const b (hψ.differentiable one_ne_zero) v y
    rw [← hdivG]
    change ∑ i, inner ℝ (b i) (fderiv ℝ (G ∘ S) (T y) (b i)) = _
    rw [hcomp]
    simp only [ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply, ContinuousLinearMap.comp_id,
      smul_apply, real_inner_smul_right, ← Finset.mul_sum]
    rfl
  have hlhs_scale :
      (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b f_r x) =
        r ^ m * ∫ y, (T ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v := by
    have htrans := integral_add_left_eq_self (μ := volume)
      (fun x ↦ E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b f_r x) x₀
    have hdil := Measure.integral_comp_smul (μ := volume)
      (f := fun u : Space (m + 1) ↦
        E.indicator (fun _ ↦ (1 : ℝ)) (x₀ + u) * fieldDivergence b f_r (x₀ + u)) r
    simp only [Space, finrank_euclideanSpace_fin, abs_inv, abs_pow,
      abs_of_pos hr_pos, smul_eq_mul] at hdil
    have hdil' :
        (∫ u : Space (m + 1),
          E.indicator (fun _ ↦ (1 : ℝ)) (x₀ + u) * fieldDivergence b f_r (x₀ + u)) =
        r ^ (m + 1) * ∫ y : Space (m + 1),
          E.indicator (fun _ ↦ (1 : ℝ)) (x₀ + r • y) * fieldDivergence b f_r (x₀ + r • y) := by
      have hrd : r ^ (m + 1) ≠ 0 := (pow_pos hr_pos (m + 1)).ne'
      calc
        _ = r ^ (m + 1) * ((r ^ (m + 1))⁻¹ * ∫ u : Space (m + 1),
            E.indicator (fun _ ↦ (1 : ℝ)) (x₀ + u) * fieldDivergence b f_r (x₀ + u)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hrd, one_mul]
        _ = _ := by rw [← hdil]
    rw [← htrans, hdil']
    have hintegrand :
        (fun y : Space (m + 1) ↦
          E.indicator (fun _ ↦ (1 : ℝ)) (x₀ + r • y) * fieldDivergence b f_r (x₀ + r • y)) =
        fun y ↦ r⁻¹ * ((T ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v) := by
      funext y
      change E.indicator (fun _ ↦ (1 : ℝ)) (T y) * fieldDivergence b f_r (T y) = _
      rw [hdiv_comp y]
      by_cases hy : y ∈ T ⁻¹' E
      · have hTy : T y ∈ E := hy
        simp [hy, hTy]
      · have hTy : T y ∉ E := hy
        simp [hy, hTy]
    rw [hintegrand, integral_const_mul, ← mul_assoc, pow_succ, mul_inv_cancel_right₀ hr_pos.ne']
  have hrhs_loc :
      (∫ x, inner ℝ (F_r x) (ν x) ∂μ.restrict Ω₀) =
        ∫ x in B_r, ψ (S x) * inner ℝ v (ν x) ∂μ := by
    have hcompl0 : (∫ x, inner ℝ (f_r x) (ν x) ∂μ.restrict Ω₀) =
        ∫ x in B_r, inner ℝ (f_r x) (ν x) ∂μ.restrict Ω₀ := by
      symm
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
      have hxnot : x ∉ tsupport f_r := fun hts ↦ hx (ball_subset_closedBall (hts_fr hts))
      simp [image_eq_zero_of_notMem_tsupport hxnot]
    change (∫ x, inner ℝ (f_r x) (ν x) ∂μ.restrict Ω₀) = _
    rw [hcompl0, Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.mpr hBr_Ω₀]
    refine setIntegral_congr_fun measurableSet_closedBall fun x _ ↦ ?_
    simp [f_r, G, real_inner_smul_left]
  change -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b f_r x) =
    ∫ x, inner ℝ (f_r x) (ν x) ∂μ.restrict Ω₀ at hpair
  change (∫ x, inner ℝ (f_r x) (ν x) ∂μ.restrict Ω₀) =
    ∫ x in B_r, ψ (S x) * inner ℝ v (ν x) ∂μ at hrhs_loc
  rw [hlhs_scale, hrhs_loc] at hpair
  have hBr_fin : μ B_r < ⊤ := (isCompact_closedBall x₀ (r * R)).measure_lt_top
  let _ : IsFiniteMeasure (μ.restrict B_r) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBr_fin⟩
  have hν_Br : IntegrableOn ν B_r μ :=
    (show IntegrableOn ν Ω₀ μ from hν_int).mono_set hBr_Ω₀
  have hψS_cont : Continuous (fun x ↦ ψ (S x)) := hψ.continuous.comp hS_cd.continuous
  have hint₁ : IntegrableOn (fun x ↦ ψ (S x) * inner ℝ v e) B_r μ :=
    (hψS_cont.mul continuous_const).continuousOn.integrableOn_compact
      (isCompact_closedBall x₀ (r * R))
  have hint₂ : IntegrableOn (fun x ↦ ψ (S x) * inner ℝ v (ν x - e)) B_r μ := by
    have hinner_int : Integrable (fun x ↦ inner ℝ v (ν x - e)) (μ.restrict B_r) :=
      (innerSL ℝ v).integrable_comp (hν_Br.sub (integrableOn_const hBr_fin.ne))
    have hmul_int := hinner_int.bdd_mul
      hψS_cont.aestronglyMeasurable (Eventually.of_forall fun x ↦ hψ_le (S x))
    exact hmul_int
  have hsplit_int :
      (∫ x in B_r, ψ (S x) * inner ℝ v (ν x) ∂μ) =
        inner ℝ v e * (∫ x in B_r, ψ (S x) ∂μ) +
          ∫ x in B_r, ψ (S x) * inner ℝ v (ν x - e) ∂μ := by
    have hpt (x : Space (m + 1)) :
        ψ (S x) * inner ℝ v (ν x) =
          ψ (S x) * inner ℝ v e + ψ (S x) * inner ℝ v (ν x - e) := by
      rw [inner_sub_right]
      ring
    simp_rw [hpt]
    rw [integral_add hint₁ hint₂, integral_mul_const, mul_comm (∫ x in B_r, ψ (S x) ∂μ)]
  have hrm_ne : r ^ m ≠ 0 := (pow_pos hr_pos m).ne'
  have hpair_scaled := congrArg (fun z : ℝ ↦ (r ^ m)⁻¹ * z) hpair
  dsimp [T, S, B_r, err] at hpair_scaled ⊢
  rw [hsplit_int] at hpair_scaled
  have hlhs_cancel :
      (r ^ m)⁻¹ * -(r ^ m * ∫ y, ((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y *
        fderiv ℝ ψ y v) =
      -(∫ y, ((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v) := by
    field_simp
  rw [hlhs_cancel] at hpair_scaled
  rw [hpair_scaled]
  ring

/-- Deterministic pointwise halfspace tangent and unit perimeter density criterion (BV12.2–BV12.4):
at *any* point `x₀ ∈ measureTheoreticBoundary E ∩ Ω₀` where the closed-ball polar oscillation
around a unit vector `e` tends to `0`, the blowups `(fun z ↦ x₀ + r • z) ⁻¹' E` converge in
`L¹_loc` along the full filter `r → 0+` to `{y | 0 < inner ℝ e y}`, and the rescaled ball and
closed-ball perimeters converge to `volume.real (closedBall (0 : Space m) 1)`. -/
theorem IsLocalPerimeterMinimizer.halfspace_tangent_of_polar_differentiation {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω Ω₀ : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (hΩ₀ : IsOpen Ω₀) (hΩ₀_sub : Ω₀ ⊆ Ω)
    (μ : Measure (Space (m + 1))) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ Ω₀ → μ U = variationalPerimeter b E U)
    {ν : Space (m + 1) → Space (m + 1)} (hν_int : Integrable ν (μ.restrict Ω₀))
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ Ω₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω₀)
    {x₀ e : Space (m + 1)} (hx₀ : x₀ ∈ measureTheoreticBoundary E ∩ Ω₀) (he : ‖e‖ = 1)
    (hosc : Tendsto (fun r ↦ (μ.real (closedBall x₀ r))⁻¹ *
      ∫ y in closedBall x₀ r, ‖ν y - e‖ ∂μ) (𝓝[>] 0) (𝓝 0)) :
    (∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun r : ℝ ↦ ∫ y in K,
        ‖((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
          {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) y‖)
        (𝓝[>] 0) (𝓝 0)) ∧
    Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
      (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
    Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (ball x₀ r))
      (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
    Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) := by
  have hd : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  let H : Set (Space (m + 1)) := {y | 0 < inner ℝ e y}
  have hH_meas : MeasurableSet H :=
    (measurableSet_Ioi (a := (0 : ℝ))).preimage
      ((continuous_const (y := e)).inner continuous_id).measurable
  obtain ⟨δ₀, hδ₀, hcb₀⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ₀.mem_nhds hx₀.2)
  have hcb₀_Ω : closedBall x₀ δ₀ ⊆ Ω := hcb₀.trans hΩ₀_sub
  -- Part 1: Full `r → 0+` halfspace blowup convergence on every compact `K`
  have hblowup : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun r : ℝ ↦ ∫ y in K,
        ‖((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
          H.indicator (fun _ ↦ (1 : ℝ)) y‖) (𝓝[>] 0) (𝓝 0) := by
    intro K₀ hK₀
    refine tendsto_nhdsGT_zero_of_subseq fun r_seq hr_pos hr_lim ↦ ?_
    let E_seq : ℕ → Set (Space (m + 1)) := fun j ↦ (fun z ↦ x₀ + r_seq j • z) ⁻¹' E
    have hmin_ball (R : ℝ) (hR : 0 < R) :
        ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) (ball 0 R) := by
      have hlt : ∀ᶠ j in atTop, r_seq j < δ₀ / R :=
        hr_lim.eventually (gt_mem_nhds (div_pos hδ₀ hR))
      filter_upwards [hlt] with j hj
      have hj_prod : r_seq j * R < δ₀ := (lt_div_iff₀ hR).mp hj
      refine (hmin.preimage_add_smul hd x₀ (hr_pos j)).mono isOpen_ball fun y hy ↦ ?_
      have hy_norm : ‖y‖ < R := by simpa [mem_ball, dist_zero_right] using hy
      apply hcb₀_Ω
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (hr_pos j).le]
      exact (mul_lt_mul_of_pos_left hy_norm (hr_pos j)).le.trans hj_prod.le
    obtain ⟨φ, C, hφ, hC_min, ht_C, -, -⟩ :=
      exists_subsequence_univ_isLocalPerimeterMinimizer_of_eventually_ball hd b E_seq hmin_ball
    let r_sub : ℕ → ℝ := fun k ↦ r_seq (φ k)
    have hr_sub_pos (k : ℕ) : 0 < r_sub k := hr_pos (φ k)
    have hr_sub_lim : Tendsto r_sub atTop (𝓝 0) := hr_lim.comp hφ.tendsto_atTop
    have hr_sub_nhdsGT : Tendsto r_sub atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hr_sub_lim, Eventually.of_forall hr_sub_pos⟩
    -- Origin remains in `measureTheoreticBoundary C`
    have h0_bdry : (0 : Space (m + 1)) ∈ measureTheoreticBoundary C := by
      intro ρ hρ
      have hc_pos : 0 < minimizerVolumeDensityConst m * ρ ^ (m + 1) :=
        mul_pos (minimizerVolumeDensityConst_pos m) (pow_pos hρ (m + 1))
      have hsmall : ∀ᶠ k in atTop, r_sub k < δ₀ / ρ :=
        hr_sub_lim.eventually (gt_mem_nhds (div_pos hδ₀ hρ))
      have hcb_sub : ∀ᶠ k in atTop,
          closedBall (0 : Space (m + 1)) ρ ⊆ (fun z ↦ x₀ + r_sub k • z) ⁻¹' Ω := by
        filter_upwards [hsmall] with k hk z hz
        have hz_le : ‖z‖ ≤ ρ := by simpa [mem_closedBall, dist_zero_right] using hz
        have hk_le : r_sub k * ρ ≤ δ₀ := ((lt_div_iff₀ hρ).mp hk).le
        apply hcb₀_Ω
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg (hr_sub_pos k).le]
        exact (mul_le_mul_of_nonneg_left hz_le (hr_sub_pos k).le).trans hk_le
      have h0_Ek (k : ℕ) : (0 : Space (m + 1)) ∈ measureTheoreticBoundary (E_seq (φ k)) := by
        rw [mem_measureTheoreticBoundary_preimage_add_smul E x₀ 0 (hr_sub_pos k)]
        simpa using hx₀.1
      have hinter_lim : Tendsto
          (fun k ↦ volume.real (E_seq (φ k) ∩ ball 0 ρ)) atTop
          (𝓝 (volume.real (C ∩ ball 0 ρ))) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
          (ht_C (closedBall 0 ρ) (isCompact_closedBall 0 ρ))
        have hEk_m : MeasurableSet (E_seq (φ k)) :=
          hmin.measurableSet.preimage (by fun_prop)
        have h1 : volume.real (E_seq (φ k) ∩ ball 0 ρ) =
            ∫ y in ball 0 ρ, (E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y := by
          rw [setIntegral_indicator hEk_m, setIntegral_const, smul_eq_mul, mul_one, inter_comm]
        have h2 : volume.real (C ∩ ball 0 ρ) =
            ∫ y in ball 0 ρ, C.indicator (fun _ ↦ (1 : ℝ)) y := by
          rw [setIntegral_indicator hC_min.measurableSet, setIntegral_const, smul_eq_mul,
            mul_one, inter_comm]
        have hi1 : IntegrableOn ((E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ))) (ball 0 ρ) volume :=
          ((continuousOn_const.integrableOn_compact (isCompact_closedBall 0 ρ)).mono_set
            ball_subset_closedBall).indicator hEk_m
        have hi2 : IntegrableOn (C.indicator (fun _ ↦ (1 : ℝ))) (ball 0 ρ) volume :=
          ((continuousOn_const.integrableOn_compact (isCompact_closedBall 0 ρ)).mono_set
            ball_subset_closedBall).indicator hC_min.measurableSet
        have hdiff_cb : IntegrableOn
            (fun y ↦ ‖(E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y -
              C.indicator (fun _ ↦ (1 : ℝ)) y‖) (closedBall 0 ρ) volume :=
          (((continuousOn_const.integrableOn_compact (isCompact_closedBall 0 ρ)).indicator hEk_m).sub
            ((continuousOn_const.integrableOn_compact (isCompact_closedBall 0 ρ)).indicator
              hC_min.measurableSet)).norm
        rw [h1, h2, ← integral_sub hi1 hi2]
        exact (norm_integral_le_integral_norm _).trans
          (setIntegral_mono_set hdiff_cb (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (Eventually.of_forall fun _ hy ↦ ball_subset_closedBall hy))
      have hsdiff_lim : Tendsto
          (fun k ↦ volume.real (ball 0 ρ \ E_seq (φ k))) atTop
          (𝓝 (volume.real (ball 0 ρ \ C))) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
          (ht_C (closedBall 0 ρ) (isCompact_closedBall 0 ρ))
        have hEk_m : MeasurableSet (E_seq (φ k)) :=
          hmin.measurableSet.preimage (by fun_prop)
        have h1 : volume.real (ball 0 ρ \ E_seq (φ k)) =
            ∫ y in ball 0 ρ, (E_seq (φ k))ᶜ.indicator (fun _ ↦ (1 : ℝ)) y := by
          have hs : ball 0 ρ \ E_seq (φ k) = ball 0 ρ ∩ (E_seq (φ k))ᶜ := rfl
          rw [hs, setIntegral_indicator hEk_m.compl, setIntegral_const, smul_eq_mul, mul_one]
        have h2 : volume.real (ball 0 ρ \ C) =
            ∫ y in ball 0 ρ, Cᶜ.indicator (fun _ ↦ (1 : ℝ)) y := by
          have hs : ball 0 ρ \ C = ball 0 ρ ∩ Cᶜ := rfl
          rw [hs, setIntegral_indicator hC_min.measurableSet.compl, setIntegral_const,
            smul_eq_mul, mul_one]
        have hi1 : IntegrableOn ((E_seq (φ k))ᶜ.indicator (fun _ ↦ (1 : ℝ))) (ball 0 ρ) volume :=
          ((continuousOn_const.integrableOn_compact (isCompact_closedBall 0 ρ)).mono_set
            ball_subset_closedBall).indicator hEk_m.compl
        have hi2 : IntegrableOn (Cᶜ.indicator (fun _ ↦ (1 : ℝ))) (ball 0 ρ) volume :=
          ((continuousOn_const.integrableOn_compact (isCompact_closedBall 0 ρ)).mono_set
            ball_subset_closedBall).indicator hC_min.measurableSet.compl
        have hpt_eq (y : Space (m + 1)) :
            ‖(E_seq (φ k))ᶜ.indicator (fun _ ↦ (1 : ℝ)) y - Cᶜ.indicator (fun _ ↦ (1 : ℝ)) y‖ =
              ‖(E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y‖ := by
          by_cases h1y : y ∈ E_seq (φ k) <;> by_cases h2y : y ∈ C <;> simp [h1y, h2y]
        have hdiff_cb : IntegrableOn
            (fun y ↦ ‖(E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y -
              C.indicator (fun _ ↦ (1 : ℝ)) y‖) (closedBall 0 ρ) volume :=
          (((continuousOn_const.integrableOn_compact (isCompact_closedBall 0 ρ)).indicator hEk_m).sub
            ((continuousOn_const.integrableOn_compact (isCompact_closedBall 0 ρ)).indicator
              hC_min.measurableSet)).norm
        rw [h1, h2, ← integral_sub hi1 hi2]
        refine (norm_integral_le_integral_norm _).trans ?_
        simp_rw [hpt_eq]
        exact setIntegral_mono_set hdiff_cb (Eventually.of_forall fun _ ↦ norm_nonneg _)
          (Eventually.of_forall fun _ hy ↦ ball_subset_closedBall hy)
      have hinter_ge : minimizerVolumeDensityConst m * ρ ^ (m + 1) ≤ volume.real (C ∩ ball 0 ρ) := by
        refine le_of_tendsto_of_tendsto tendsto_const_nhds hinter_lim ?_
        filter_upwards [hcb_sub] with k hk
        exact (hmin.preimage_add_smul hd x₀ (hr_sub_pos k)).volume_inter_ball_ge (h0_Ek k) hρ hk
      have hsdiff_ge : minimizerVolumeDensityConst m * ρ ^ (m + 1) ≤ volume.real (ball 0 ρ \ C) := by
        refine le_of_tendsto_of_tendsto tendsto_const_nhds hsdiff_lim ?_
        filter_upwards [hcb_sub] with k hk
        exact (hmin.preimage_add_smul hd x₀ (hr_sub_pos k)).volume_sdiff_ball_ge (h0_Ek k) hρ hk
      refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
      · simp [Measure.real, h0] at hinter_ge
        linarith
      · simp [Measure.real, h0] at hsdiff_ge
        linarith
    -- Convergence of directional pairings along `φ`
    have hlhs_tendsto (ψ : Space (m + 1) → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ)
        (v : Space (m + 1)) :
        Tendsto (fun k ↦ -(∫ y, (E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v))
          atTop (𝓝 (-(∫ y, C.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v))) := by
      refine Tendsto.neg ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hfd_cont : Continuous (fun y ↦ fderiv ℝ ψ y v) :=
        (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp (hψ.continuous_fderiv one_ne_zero)
      have hfd_hc : HasCompactSupport (fun y ↦ fderiv ℝ ψ y v) :=
        hcψ.of_isClosed_subset (isClosed_tsupport _)
          (closure_minimal (fun y hy ↦ by
            by_contra hnot
            exact hy (by simp [fderiv_of_notMem_tsupport ℝ hnot])) (isClosed_tsupport ψ))
      obtain ⟨M₀, hM₀⟩ := hfd_hc.exists_bound_of_continuous hfd_cont
      let M : ℝ := max M₀ 0
      have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
      have hfd_le (y : Space (m + 1)) : ‖fderiv ℝ ψ y v‖ ≤ M := (hM₀ y).trans (le_max_left M₀ 0)
      have hlim0 : Tendsto
          (fun k ↦ M * ∫ y in tsupport ψ,
            ‖(E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y - C.indicator (fun _ ↦ (1 : ℝ)) y‖)
          atTop (𝓝 0) := by
        simpa only [mul_zero] using (ht_C (tsupport ψ) hcψ).const_mul M
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hlim0
      have hEk_m : MeasurableSet (E_seq (φ k)) := hmin.measurableSet.preimage (by fun_prop)
      have hloc_int (A : Set (Space (m + 1))) :
          (∫ y, A.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v) =
            ∫ y in tsupport ψ, A.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v := by
        symm
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_
        have hz : fderiv ℝ ψ y = 0 := fderiv_of_notMem_tsupport ℝ hy
        simp [hz]
      have hi_k : IntegrableOn
          (fun y ↦ (E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v)
          (tsupport ψ) volume := by
        have heq : (fun y ↦ (E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v) =
            (E_seq (φ k)).indicator (fun y ↦ fderiv ℝ ψ y v) := by
          funext y; by_cases hy : y ∈ E_seq (φ k) <;> simp [hy]
        rw [heq]
        exact (hfd_cont.continuousOn.integrableOn_compact hcψ).indicator hEk_m
      have hi_C : IntegrableOn
          (fun y ↦ C.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v)
          (tsupport ψ) volume := by
        have heq : (fun y ↦ C.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v) =
            C.indicator (fun y ↦ fderiv ℝ ψ y v) := by
          funext y; by_cases hy : y ∈ C <;> simp [hy]
        rw [heq]
        exact (hfd_cont.continuousOn.integrableOn_compact hcψ).indicator hC_min.measurableSet
      have hdiff_int : IntegrableOn
          (fun y ↦ ‖(E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y -
            C.indicator (fun _ ↦ (1 : ℝ)) y‖) (tsupport ψ) volume :=
        (((continuousOn_const.integrableOn_compact hcψ).indicator hEk_m).sub
          ((continuousOn_const.integrableOn_compact hcψ).indicator hC_min.measurableSet)).norm
      rw [hloc_int (E_seq (φ k)), hloc_int C, ← integral_sub hi_k hi_C]
      calc
        ‖∫ y in tsupport ψ,
            ((E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v -
              C.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v)‖ ≤
          ∫ y in tsupport ψ,
            ‖(E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v -
              C.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ y in tsupport ψ,
            M * ‖(E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y -
              C.indicator (fun _ ↦ (1 : ℝ)) y‖ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (hdiff_int.const_mul M) (Eventually.of_forall fun y ↦ ?_)
          dsimp only
          rw [← sub_mul, norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hfd_le y) (norm_nonneg _)
        _ = M * ∫ y in tsupport ψ,
            ‖(E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y -
              C.indicator (fun _ ↦ (1 : ℝ)) y‖ := integral_const_mul _ _
    -- Weak directional properties of `C`
    have horth : ∀ ψ : Space (m + 1) → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        ∀ v : Space (m + 1), inner ℝ e v = 0 →
          (∫ y, C.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v) = 0 := by
      intro ψ hψ hcψ v hv
      obtain ⟨R, err, -, herr, hdecomp⟩ :=
        rescaled_directional_pairing_decomposition hmin hΩ₀ hΩ₀_sub μ hμ hν_int hdist
          hx₀.2 hosc hψ hcψ v
      have hve : inner ℝ v e = 0 := by rw [real_inner_comm, hv]
      have hrhs_lim : Tendsto
          (fun k ↦ -(∫ y, (E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y v))
          atTop (𝓝 0) := by
        refine (herr.comp hr_sub_nhdsGT).congr' ?_
        filter_upwards [hr_sub_nhdsGT.eventually hdecomp] with k hk
        simp [E_seq, r_sub, hve] at hk ⊢
        exact hk.symm
      have heq := tendsto_nhds_unique (hlhs_tendsto ψ hψ hcψ v) hrhs_lim
      exact neg_eq_zero.mp heq
    have hmono : ∀ ψ : Space (m + 1) → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∀ y, 0 ≤ ψ y) →
          0 ≤ -(∫ y, C.indicator (fun _ ↦ (1 : ℝ)) y * fderiv ℝ ψ y e) := by
      intro ψ hψ hcψ hψ_nonneg
      obtain ⟨R, err, -, herr, hdecomp⟩ :=
        rescaled_directional_pairing_decomposition hmin hΩ₀ hΩ₀_sub μ hμ hν_int hdist
          hx₀.2 hosc hψ hcψ e
      have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
      refine le_of_tendsto_of_tendsto (herr.comp hr_sub_nhdsGT) (hlhs_tendsto ψ hψ hcψ e) ?_
      filter_upwards [hr_sub_nhdsGT.eventually hdecomp] with k hk
      dsimp [E_seq, r_sub] at hk ⊢
      rw [hk, hee, one_mul]
      have hmain_nonneg : 0 ≤ ((r_seq (φ k)) ^ m)⁻¹ *
          ∫ x in closedBall x₀ (r_seq (φ k) * R), ψ ((r_seq (φ k))⁻¹ • (x - x₀)) ∂μ :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg (hr_sub_pos k).le m))
          (integral_nonneg fun x ↦ hψ_nonneg _)
      linarith
    have hC_eq_H : C =ᵐ[volume] H :=
      ae_eq_positive_halfspace_of_weak_directional_deriv hC_min.measurableSet h0_bdry he horth hmono
    have hC_ind_H : C.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[volume] H.indicator (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [hC_eq_H] with y hy
      by_cases hyC : y ∈ C
      · have hyH : y ∈ H := hy ▸ hyC
        simp [hyC, hyH]
      · have hyH : y ∉ H := fun hh ↦ hyC (hy.symm ▸ hh)
        simp [hyC, hyH]
    refine ⟨φ, hφ, (ht_C K₀ hK₀).congr fun k ↦ ?_⟩
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hC_ind_H] with y hy
    dsimp [E_seq]
    rw [hy]
  -- Part 2: Unit perimeter density on open balls (`variationalPerimeter` and `μ.real (ball x₀ r)`)
  have hdensity_P : Tendsto
      (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
      (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) := by
    refine tendsto_nhdsGT_zero_of_subseq fun r_seq hr_pos hr_lim ↦ ?_
    let E_seq : ℕ → Set (Space (m + 1)) := fun j ↦ (fun z ↦ x₀ + r_seq j • z) ⁻¹' E
    have hr_nhdsGT : Tendsto r_seq atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hr_lim, Eventually.of_forall hr_pos⟩
    have hmin_ball2 : ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) (ball 0 2) := by
      have hlt : ∀ᶠ j in atTop, r_seq j < δ₀ / 2 :=
        hr_lim.eventually (gt_mem_nhds (half_pos hδ₀))
      filter_upwards [hlt] with j hj
      refine (hmin.preimage_add_smul hd x₀ (hr_pos j)).mono isOpen_ball fun y hy ↦ ?_
      have hy_norm : ‖y‖ < 2 := by simpa [mem_ball, dist_zero_right] using hy
      apply hcb₀_Ω
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (hr_pos j).le]
      nlinarith [hr_pos j]
    have ht_seq (K : Set (Space (m + 1))) (hK : IsCompact K) (_ : K ⊆ ball 0 2) :
        Tendsto (fun j ↦ ∫ y in K,
          ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) y - H.indicator (fun _ ↦ (1 : ℝ)) y‖)
          atTop (𝓝 0) :=
      (hblowup K hK).comp hr_nhdsGT
    have hH_cont : Tendsto (fun s ↦ variationalPerimeter b H (ball 0 s)) (𝓝[>] 1)
        (𝓝 (variationalPerimeter b H (ball 0 1))) := by
      let g : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ m * volume.real (closedBall (0 : Space m) 1))
      have hg_cont : Continuous g :=
        ENNReal.continuous_ofReal.comp ((continuous_pow m).mul continuous_const)
      have hg_eq {s : ℝ} (hs : 0 < s) : variationalPerimeter b H (ball 0 s) = g s := by
        have hfin : variationalPerimeter b H (ball 0 s) ≠ ⊤ := by
          rw [positive_halfspace_perimeter_closedBall_volume b he hs]
          exact (isCompact_closedBall (0 : Space m) s).measure_lt_top.ne
        rw [← ENNReal.ofReal_toReal hfin, positive_halfspace_perimeter_toReal b he hs]
      have hg_lim : Tendsto g (𝓝[>] 1) (𝓝 (g 1)) :=
        hg_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      rw [← hg_eq zero_lt_one] at hg_lim
      refine hg_lim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      exact (hg_eq (zero_lt_one.trans hs)).symm
    have hP_unit := tendsto_variationalPerimeter_ball_toReal_of_eventually_right_continuous
      hd b hmin_ball2 hH_meas ht_seq zero_lt_one (closedBall_subset_ball one_lt_two) hH_cont
    rw [positive_halfspace_perimeter_toReal b he zero_lt_one, one_pow, one_mul] at hP_unit
    refine ⟨id, strictMono_id, hP_unit.congr fun j ↦ ?_⟩
    have hscale := variationalPerimeter_preimage_add_smul_ball hd b E x₀ 0 (hr_pos j) (ρ := 1)
    simp only [Nat.add_sub_cancel, smul_zero, add_zero, mul_one] at hscale
    change (variationalPerimeter b (E_seq j) (ball 0 1)).toReal = _
    rw [hscale, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (hr_pos j).le m)),
      zpow_neg, zpow_natCast]
    rfl
  have hdensity_μ_ball : Tendsto
      (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (ball x₀ r))
      (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) := by
    refine hdensity_P.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT hδ₀] with r hr
    have hsub_r : ball x₀ r ⊆ Ω₀ :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hr.2)).trans hcb₀
    simp [Measure.real, hμ (ball x₀ r) isOpen_ball hsub_r]
  -- Part 3: Unit perimeter density on closed balls `μ.real (closedBall x₀ r)`
  have hdensity_μ_closedBall : Tendsto
      (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) := by
    let ω_m : ℝ := volume.real (closedBall (0 : Space m) 1)
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [Ioc_mem_nhdsGT hδ₀,
        (tendsto_order.mp hdensity_μ_ball).1 a ha] with r hr hgt
      have hfin_cb : μ (closedBall x₀ r) ≠ ⊤ :=
        (isCompact_closedBall x₀ r).measure_lt_top.ne
      have hmono : μ.real (ball x₀ r) ≤ μ.real (closedBall x₀ r) :=
        measureReal_mono ball_subset_closedBall hfin_cb
      have hr_nonneg : 0 ≤ r ^ (-(m : ℤ)) := zpow_nonneg hr.1.le _
      exact hgt.trans_le (mul_le_mul_of_nonneg_left hmono hr_nonneg)
    · intro M hM
      have hcont_pow : Continuous (fun α : ℝ ↦ α ^ m * ω_m) :=
        (continuous_pow m).mul continuous_const
      have hlim_α : Tendsto (fun α : ℝ ↦ α ^ m * ω_m) (𝓝[>] 1) (𝓝 ω_m) := by
        have h0 := hcont_pow.tendsto 1
        simp only [one_pow, one_mul] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      obtain ⟨α, hα_gt, hα_lt⟩ :=
        ((hlim_α.eventually (gt_mem_nhds hM)).and self_mem_nhdsWithin).exists
      have hα_pos : 0 < α := zero_lt_one.trans hα_lt
      have hmul_α : Tendsto (fun r : ℝ ↦ α * r) (𝓝[>] 0) (𝓝[>] 0) := by
        have h0 : Tendsto (fun r : ℝ ↦ α * r) (𝓝 0) (𝓝 (α * 0)) :=
          ((continuous_const (y := α)).mul continuous_id).tendsto 0
        rw [mul_zero] at h0
        exact tendsto_nhdsWithin_iff.mpr
          ⟨h0.mono_left nhdsWithin_le_nhds, by
            filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
            exact mul_pos hα_pos hr⟩
      have hscaled_lim : Tendsto
          (fun r : ℝ ↦ α ^ m * ((α * r) ^ (-(m : ℤ)) * μ.real (ball x₀ (α * r))))
          (𝓝[>] 0) (𝓝 (α ^ m * ω_m)) :=
        ((hdensity_μ_ball.comp hmul_α).congr fun _ ↦ rfl).const_mul (α ^ m)
      filter_upwards [self_mem_nhdsWithin,
        hscaled_lim.eventually (gt_mem_nhds hα_gt)] with r (hr : 0 < r) hlt_M
      have hr_lt_αr : r < α * r := lt_mul_of_one_lt_left hr hα_lt
      have hfin_ball : μ (ball x₀ (α * r)) ≠ ⊤ :=
        ((measure_mono ball_subset_closedBall).trans_lt
          (isCompact_closedBall x₀ (α * r)).measure_lt_top).ne
      have hmono : μ.real (closedBall x₀ r) ≤ μ.real (ball x₀ (α * r)) :=
        measureReal_mono (closedBall_subset_ball hr_lt_αr) hfin_ball
      have hident : r ^ (-(m : ℤ)) * μ.real (ball x₀ (α * r)) =
          α ^ m * ((α * r) ^ (-(m : ℤ)) * μ.real (ball x₀ (α * r))) := by
        rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, mul_pow]
        have hαm_ne : α ^ m ≠ 0 := (pow_pos hα_pos m).ne'
        have hrm_ne : r ^ m ≠ 0 := (pow_pos hr m).ne'
        field_simp
      have hle : r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r) ≤
          α ^ m * ((α * r) ^ (-(m : ℤ)) * μ.real (ball x₀ (α * r))) := by
        rw [← hident]
        exact mul_le_mul_of_nonneg_left hmono (zpow_nonneg hr.le _)
      exact hle.trans_lt hlt_M
  exact ⟨hblowup, hdensity_P, hdensity_μ_ball, hdensity_μ_closedBall⟩

/-! ### 4. Almost-everywhere halfspace tangents and unit perimeter density (local & global) -/

/-- Local `(μ.restrict Ω₀)`-a.e. halfspace tangent and unit perimeter density theorem on an open
region `Ω₀ ⊆ Ω` carrying a polar representation `(μ, ν)` (BV12). -/
theorem IsLocalPerimeterMinimizer.ae_halfspace_tangent_on_open {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω Ω₀ : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (hΩ₀ : IsOpen Ω₀) (hΩ₀_sub : Ω₀ ⊆ Ω)
    (μ : Measure (Space (m + 1))) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ Ω₀ → μ U = variationalPerimeter b E U)
    {ν : Space (m + 1) → Space (m + 1)} (hν_int : Integrable ν (μ.restrict Ω₀))
    (hν_norm : ∀ᵐ x ∂μ.restrict Ω₀, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ Ω₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω₀) :
    ∀ᵐ x₀ ∂μ.restrict Ω₀,
      x₀ ∈ measureTheoreticBoundary E ∩ Ω₀ ∧
      ‖ν x₀‖ = 1 ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun r : ℝ ↦ ∫ y in K,
          ‖((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
            {y : Space (m + 1) | 0 < inner ℝ (ν x₀) y}.indicator (fun _ ↦ (1 : ℝ)) y‖)
          (𝓝[>] 0) (𝓝 0)) ∧
      Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
        (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
      Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (ball x₀ r))
        (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
      Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r))
        (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) := by
  have hsupp_eq := (hmin.mono hΩ₀ hΩ₀_sub).support_measure_inter_eq μ hμ
  filter_upwards [ae_polar_besicovitch_differentiation μ hΩ₀ hν_int hν_norm]
    with x₀ ⟨hx₀_Ω₀, hx₀_supp, hν_x₀, _, hosc⟩
  have hx₀_bdry : x₀ ∈ measureTheoreticBoundary E ∩ Ω₀ := by
    rw [← hsupp_eq]
    exact ⟨hx₀_supp, hx₀_Ω₀⟩
  have hpt := hmin.halfspace_tangent_of_polar_differentiation hΩ₀ hΩ₀_sub μ hμ hν_int hdist
    hx₀_bdry hν_x₀ hosc
  exact ⟨hx₀_bdry, hν_x₀, hpt.1, hpt.2.1, hpt.2.2.1, hpt.2.2.2⟩

/-- Domain-wide `(μ.restrict Ω)`-a.e. existence of halfspace tangents and unit perimeter density
for any local perimeter minimizer `IsLocalPerimeterMinimizer b E Ω` and any locally finite measure
`μ` agreeing with `variationalPerimeter b E` on open subsets of `Ω` (BV12, general open domain). -/
theorem IsLocalPerimeterMinimizer.ae_exists_halfspace_tangent_on_domain {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω)
    (μ : Measure (Space (m + 1))) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U) :
    ∀ᵐ x₀ ∂μ.restrict Ω,
      ∃ e : Space (m + 1),
        x₀ ∈ measureTheoreticBoundary E ∩ Ω ∧
        ‖e‖ = 1 ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun r : ℝ ↦ ∫ y in K,
            ‖((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
              {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) y‖)
            (𝓝[>] 0) (𝓝 0)) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (ball x₀ r))
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r))
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) := by
  let K_seq : ℕ → Set (Space (m + 1)) := fun j ↦
    closedBall 0 ((j : ℝ) + 1) \ thickening (1 / ((j : ℝ) + 1)) Ωᶜ
  have hK_comp (j : ℕ) : IsCompact (K_seq j) :=
    (isCompact_closedBall 0 ((j : ℝ) + 1)).diff isOpen_thickening
  have hK_sub (j : ℕ) : K_seq j ⊆ Ω := by
    intro x ⟨_, hx_not⟩
    by_contra hxΩ
    exact hx_not (self_subset_thickening (by positivity) Ωᶜ hxΩ)
  have hK_union : (⋃ j : ℕ, K_seq j) = Ω := by
    apply Subset.antisymm (iUnion_subset hK_sub)
    intro x hxΩ
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hmin.isOpen_domain x hxΩ
    obtain ⟨n₁, hn₁⟩ := exists_nat_gt ‖x‖
    obtain ⟨n₂, hn₂⟩ := exists_nat_one_div_lt hr
    let j := max n₁ n₂
    refine mem_iUnion.mpr ⟨j, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have hle : (n₁ : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_max_left n₁ n₂
      linarith
    · intro hxt
      rw [mem_thickening_iff] at hxt
      obtain ⟨y, hyΩc, hdist⟩ := hxt
      have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((n₂ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right (le_max_right n₁ n₂) 1)
      have hy_ball : y ∈ ball x r := by
        rw [mem_ball, dist_comm]
        linarith
      exact hyΩc (hball hy_ball)
  let P : Space (m + 1) → Prop := fun x₀ ↦
    ∃ e : Space (m + 1),
      x₀ ∈ measureTheoreticBoundary E ∩ Ω ∧
      ‖e‖ = 1 ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun r : ℝ ↦ ∫ y in K,
          ‖((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
            {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) y‖)
          (𝓝[>] 0) (𝓝 0)) ∧
      Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
        (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
      Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (ball x₀ r))
        (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
      Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r))
        (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1)))
  have h_on_ball (c : Space (m + 1)) {r : ℝ} (hr : 0 < r) (hcb : closedBall c r ⊆ Ω) :
      ∀ᵐ x₀ ∂μ.restrict (ball c r), P x₀ := by
    obtain ⟨δ, μ_loc, ν_loc, hδ, hcb_δ, hfin_loc, hzero_loc, hμ_loc, hν_int_loc, hν_norm_loc,
      hdist_loc⟩ := hmin.exists_ball_radon_measure hr hcb
    let B := ball c (r + δ)
    have hB_Ω : B ⊆ Ω := ball_subset_closedBall.trans hcb_δ
    let _ : IsFiniteMeasure μ_loc := hfin_loc
    let _ : IsFiniteMeasure (μ.restrict B) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall c (r + δ)).measure_lt_top)⟩
    have hres_eq : μ.restrict B = μ_loc := by
      have hself : (μ.restrict B).restrict B = μ.restrict B :=
        Measure.restrict_restrict_of_subset Subset.rfl
      rw [← hself]
      exact measure_restrict_eq_of_open_values isOpen_ball hzero_loc fun U hU hUB ↦ by
        rw [Measure.restrict_apply hU.measurableSet, inter_eq_left.mpr hUB,
          hμ_loc U hU hUB, hμ U hU (hUB.trans hB_Ω)]
    have hν_int_B : Integrable ν_loc (μ.restrict B) := by rwa [hres_eq]
    have hν_norm_B : ∀ᵐ x ∂μ.restrict B, ‖ν_loc x‖ = 1 := by rwa [hres_eq]
    have hdist_B : ∀ F : C_c(Space (m + 1), Space (m + 1)),
        ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
        tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ B →
        -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
          ∫ x, inner ℝ (F x) (ν_loc x) ∂μ.restrict B := by
      intro F hF hs
      rw [hres_eq]
      exact hdist_loc F hF hs
    have hae_B := hmin.ae_halfspace_tangent_on_open isOpen_ball hB_Ω μ
      (fun U hU hUB ↦ hμ U hU (hUB.trans hB_Ω)) hν_int_B hν_norm_B hdist_B
    have hae_sub : ∀ᵐ x₀ ∂μ.restrict (ball c r), _ :=
      ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith : r ≤ r + δ)) hae_B
    filter_upwards [hae_sub] with x₀ hx₀
    exact ⟨ν_loc x₀, ⟨hx₀.1.1, hB_Ω hx₀.1.2⟩, hx₀.2.1, hx₀.2.2.1, hx₀.2.2.2.1,
      hx₀.2.2.2.2.1, hx₀.2.2.2.2.2⟩
  have h_on_K (j : ℕ) : ∀ᵐ x₀ ∂μ.restrict (K_seq j), P x₀ := by
    have hball_ex : ∀ x ∈ K_seq j, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ Ω := fun x hx ↦
      Metric.nhds_basis_closedBall.mem_iff.mp (hmin.isOpen_domain.mem_nhds (hK_sub j hx))
    choose! r_x hr_x hcb_x using hball_ex
    obtain ⟨F_fin, hcov⟩ := (hK_comp j).elim_finite_subcover
      (fun x : K_seq j ↦ ball (x : Space (m + 1)) (r_x x))
      (fun _ ↦ isOpen_ball)
      (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr_x x hx)⟩)
    let U_j := ⋃ x ∈ F_fin, ball (x : Space (m + 1)) (r_x x)
    have hae_Uj : ∀ᵐ x₀ ∂μ.restrict U_j, P x₀ := by
      rw [ae_restrict_biUnion_finset_iff]
      intro x _
      exact h_on_ball x (hr_x x x.2) (hcb_x x x.2)
    exact ae_restrict_of_ae_restrict_of_subset hcov hae_Uj
  have hall : ∀ᵐ x₀ ∂μ.restrict (⋃ j, K_seq j), P x₀ :=
    (ae_restrict_iUnion_iff K_seq P).mpr h_on_K
  rwa [hK_union] at hall

/-- Global `μ`-a.e. halfspace tangent and unit perimeter density theorem for a global perimeter
minimizer `IsLocalPerimeterMinimizer b E univ` and any locally finite measure `μ` agreeing with
`variationalPerimeter b E` on open sets (BV12). -/
theorem IsLocalPerimeterMinimizer.ae_exists_halfspace_tangent_of_measure {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ)
    (μ : Measure (Space (m + 1))) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → μ U = variationalPerimeter b E U) :
    ∀ᵐ x₀ ∂μ,
      ∃ e : Space (m + 1),
        x₀ ∈ measureTheoreticBoundary E ∧
        ‖e‖ = 1 ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun r : ℝ ↦ ∫ y in K,
            ‖((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
              {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) y‖)
            (𝓝[>] 0) (𝓝 0)) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (ball x₀ r))
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r))
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) := by
  let Ω_seq : ℕ → Set (Space (m + 1)) := fun k ↦ ball 0 ((k : ℝ) + 1)
  have h_on_k (k : ℕ) : ∀ᵐ x₀ ∂μ.restrict (Ω_seq k),
      ∃ e : Space (m + 1),
        x₀ ∈ measureTheoreticBoundary E ∧
        ‖e‖ = 1 ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun r : ℝ ↦ ∫ y in K,
            ‖((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
              {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) y‖)
            (𝓝[>] 0) (𝓝 0)) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (ball x₀ r))
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * μ.real (closedBall x₀ r))
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) := by
    have hPk : variationalPerimeter b E (Ω_seq k) ≠ ⊤ :=
      hmin.perimeter_ball_ne_top 0 ((k : ℝ) + 1) (by positivity) (subset_univ _)
    obtain ⟨ν_k, hν_int, hν_norm, hdist⟩ :=
      exists_local_polar_for_perimeter_measure b hmin.measurableSet isOpen_ball hPk μ hμ
    filter_upwards [hmin.ae_halfspace_tangent_on_open isOpen_ball (subset_univ _) μ
      (fun U hU _ ↦ hμ U hU) hν_int hν_norm hdist] with x₀ hx₀
    exact ⟨ν_k x₀, hx₀.1.1, hx₀.2.1, hx₀.2.2.1, hx₀.2.2.2.1, hx₀.2.2.2.2.1, hx₀.2.2.2.2.2⟩
  have hiUnion : (⋃ k : ℕ, Ω_seq k) = univ := by
    refine eq_univ_of_forall fun x ↦ mem_iUnion.mpr ?_
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    exact ⟨k, by simp only [Ω_seq, mem_ball, dist_zero_right]; linarith⟩
  have hall := (ae_restrict_iUnion_iff Ω_seq _).mpr h_on_k
  simpa only [hiUnion, Measure.restrict_univ] using hall

/-- Global `perimeterRadonMeasure`-a.e. halfspace tangent and unit perimeter density theorem for
`hmin : IsLocalPerimeterMinimizer b E univ` (BV12). -/
theorem IsLocalPerimeterMinimizer.ae_exists_halfspace_tangent_global {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ)
    (hP : ∀ n : ℕ, variationalPerimeter b E (ball 0 ((n : ℝ) + 1)) ≠ ⊤ :=
      fun n ↦ hmin.perimeter_ball_ne_top 0 ((n : ℝ) + 1) (by positivity) (subset_univ _)) :
    ∀ᵐ x₀ ∂perimeterRadonMeasure b hmin.measurableSet hP,
      ∃ e : Space (m + 1),
        x₀ ∈ measureTheoreticBoundary E ∧
        ‖e‖ = 1 ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun r : ℝ ↦ ∫ y in K,
            ‖((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
              {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) y‖)
            (𝓝[>] 0) (𝓝 0)) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) *
          (perimeterRadonMeasure b hmin.measurableSet hP).real (ball x₀ r))
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) ∧
        Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) *
          (perimeterRadonMeasure b hmin.measurableSet hP).real (closedBall x₀ r))
          (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) :=
  hmin.ae_exists_halfspace_tangent_of_measure (perimeterRadonMeasure b hmin.measurableSet hP)
    fun _ hU ↦ perimeterRadonMeasure_apply_open b hmin.measurableSet hP hU

end SerrinEpigraph
