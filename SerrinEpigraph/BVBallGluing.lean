module

public import SerrinEpigraph.BVCutoff
public import SerrinEpigraph.PerimeterLocality
public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Spherical slicing and ball gluing for finite-perimeter phases

Given two measurable phases `F` and `E`, gluing `F` inside `ball x₀ r` to `E` outside `ball x₀ r`
produces a competitor whose variational perimeter is controlled by the inner perimeter mass of `F`,
the outer perimeter mass of `E`, and the radial derivative of the symmetric-difference ball volume.
No boundary rectifiability or general Lipschitz trace theorem is assumed.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology CompactlySupported ENNReal

namespace SerrinEpigraph

/-- Gluing phase `F` inside `ball x₀ r` with phase `E` outside `ball x₀ r`. -/
def ballGluedSet {d : ℕ} (x₀ : Space d) (r : ℝ) (F E : Set (Space d)) : Set (Space d) :=
  (F ∩ ball x₀ r) ∪ (E \ ball x₀ r)

/-- Explicit positive radial cutoff constant used in ball gluing bounds. -/
def ballGluingConstant : ℝ :=
  Classical.choose exists_fixedWidth_ball_cutoffs

/-- Positivity of `ballGluingConstant`. -/
theorem ballGluingConstant_pos : 0 < ballGluingConstant :=
  (Classical.choose_spec exists_fixedWidth_ball_cutoffs).1

theorem measurableSet_ballGluedSet {d : ℕ} (x₀ : Space d) (r : ℝ) {F E : Set (Space d)}
    (hF : MeasurableSet F) (hE : MeasurableSet E) :
    MeasurableSet (ballGluedSet x₀ r F E) :=
  (hF.inter measurableSet_ball).union (hE.diff measurableSet_ball)

@[simp]
theorem ballGluedSet_empty_left {d : ℕ} (x₀ : Space d) (r : ℝ) (E : Set (Space d)) :
    ballGluedSet x₀ r ∅ E = E \ ball x₀ r := by
  ext x
  simp [ballGluedSet]

@[simp]
theorem ballGluedSet_empty_right {d : ℕ} (x₀ : Space d) (r : ℝ) (F : Set (Space d)) :
    ballGluedSet x₀ r F ∅ = F ∩ ball x₀ r := by
  ext x
  simp [ballGluedSet]

@[simp]
theorem ballGluedSet_self {d : ℕ} (x₀ : Space d) (r : ℝ) (E : Set (Space d)) :
    ballGluedSet x₀ r E E = E :=
  inter_union_sdiff E (ball x₀ r)

theorem mem_ballGluedSet_of_mem_ball {d : ℕ} {x₀ x : Space d} {r : ℝ}
    {F E : Set (Space d)} (hx : x ∈ ball x₀ r) :
    x ∈ ballGluedSet x₀ r F E ↔ x ∈ F := by
  simp [ballGluedSet, hx]

theorem mem_ballGluedSet_of_notMem_ball {d : ℕ} {x₀ x : Space d} {r : ℝ}
    {F E : Set (Space d)} (hx : x ∉ ball x₀ r) :
    x ∈ ballGluedSet x₀ r F E ↔ x ∈ E := by
  simp [ballGluedSet, hx]

@[simp]
theorem variationalPerimeter_empty {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (Ω : Set (Space d)) :
    variationalPerimeter b ∅ Ω = 0 := by
  unfold variationalPerimeter
  simp

/-! ### Translated radial cutoffs and localized distributional product bounds -/

private theorem exists_pos_closedBall_add_subset {d : ℕ} {x₀ : Space d} {r : ℝ}
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (hsub : closedBall x₀ r ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ closedBall x₀ (r + δ) ⊆ Ω := by
  let K' := closedBall x₀ (r + 1) \ Ω
  have hK' : IsCompact K' := (isCompact_closedBall x₀ (r + 1)).diff hΩ
  rcases K'.eq_empty_or_nonempty with hK'e | hK'ne
  · refine ⟨1, zero_lt_one, fun y hy ↦ ?_⟩
    by_contra hyΩ
    have hyK' : y ∈ K' := ⟨hy, hyΩ⟩
    rw [hK'e] at hyK'
    exact hyK'
  · obtain ⟨y₀, hy₀, hmin⟩ :=
      hK'.exists_isMinOn hK'ne (continuous_id.dist continuous_const).continuousOn
    have hy₀_not : y₀ ∉ closedBall x₀ r := fun h ↦ hy₀.2 (hsub h)
    have hr_lt : r < dist y₀ x₀ := lt_of_not_ge (by simpa [mem_closedBall] using hy₀_not)
    have hy₀_le : dist y₀ x₀ ≤ r + 1 := mem_closedBall.mp hy₀.1
    refine ⟨(dist y₀ x₀ - r) / 2, by linarith, fun y hy ↦ ?_⟩
    have hydist : dist y x₀ ≤ r + (dist y₀ x₀ - r) / 2 := mem_closedBall.mp hy
    have hy1 : y ∈ closedBall x₀ (r + 1) := mem_closedBall.mpr (by linarith)
    by_contra hyΩ
    have hle : dist y₀ x₀ ≤ dist y x₀ := hmin ⟨hy1, hyΩ⟩
    linarith

set_option backward.isDefEq.respectTransparency false in
private theorem exists_translated_ball_cutoff {d : ℕ} (x₀ : Space d) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    ∃ φ : Space d → ℝ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ ball x₀ (r + ε) ∧
      (∀ x ∈ ball x₀ r, φ x = 1) ∧
      (∀ x ∈ closedBall x₀ r, φ x = 1) ∧
      (∀ x, φ x ∈ Icc (0 : ℝ) 1) ∧
      ∀ x, ‖gradient φ x‖ ≤ ballGluingConstant / ε := by
  obtain ⟨χ, hχ, _, hsχ, honeχ, hvalχ, hgradχ⟩ :=
    (Classical.choose_spec exists_fixedWidth_ball_cutoffs).2 d r ε hr hε
  let φ : Space d → ℝ := fun x ↦ χ (x - x₀)
  have hφ : ContDiff ℝ 1 φ := hχ.comp (contDiff_id.sub contDiff_const)
  have hsφ : tsupport φ ⊆ ball x₀ (r + ε) := by
    intro x hx
    have hpre : Function.support φ = (fun y : Space d ↦ y - x₀) ⁻¹' Function.support χ := rfl
    have hcl : x ∈ (fun y : Space d ↦ y - x₀) ⁻¹' tsupport χ := by
      have hh := Continuous.closure_preimage_subset (f := fun y : Space d ↦ y - x₀)
        (continuous_id.sub (continuous_const (y := x₀))) (Function.support χ)
      rw [← hpre] at hh
      exact hh hx
    have hmem : x - x₀ ∈ ball (0 : Space d) (r + ε) := hsχ hcl
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hmem
  have hcφ : HasCompactSupport φ :=
    (isCompact_closedBall x₀ (r + ε)).of_isClosed_subset (isClosed_tsupport _)
      (hsφ.trans ball_subset_closedBall)
  have hone_ball : ∀ x ∈ ball x₀ r, φ x = 1 := by
    intro x hx
    apply honeχ
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hx
  have hone_closed : ∀ x ∈ closedBall x₀ r, φ x = 1 := by
    intro x hx
    let t : ℕ → ℝ := fun n ↦ (n : ℝ) / ((n : ℝ) + 1)
    let y : ℕ → Space d := fun n ↦ x₀ + t n • (x - x₀)
    have hy_ball : ∀ n, y n ∈ ball x₀ r := by
      intro n
      have htn0 : 0 ≤ t n := by dsimp [t]; positivity
      have htn1 : t n < 1 := by
        dsimp [t]
        rw [div_lt_one (by positivity)]
        linarith
      have hdist : ‖x - x₀‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hx
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htn0]
      calc
        t n * ‖x - x₀‖ ≤ t n * r := mul_le_mul_of_nonneg_left hdist htn0
        _ < 1 * r := mul_lt_mul_of_pos_right htn1 hr
        _ = r := one_mul r
    have ht_lim : Tendsto t atTop (𝓝 1) := by
      have heq : t = fun n : ℕ ↦ 1 - 1 / ((n : ℝ) + 1) := by
        funext n
        dsimp [t]
        field_simp
        ring
      rw [heq]
      have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [sub_zero] using hh
    have hy_lim : Tendsto y atTop (𝓝 x) := by
      have hh := (tendsto_const_nhds (x := x₀)).add (ht_lim.smul_const (x - x₀))
      simpa [y] using hh
    have hφy : Tendsto (fun n ↦ φ (y n)) atTop (𝓝 (φ x)) :=
      (hφ.continuous.tendsto x).comp hy_lim
    have hφ1 : Tendsto (fun n ↦ φ (y n)) atTop (𝓝 1) := by
      simp_rw [hone_ball _ (hy_ball _)]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hφy hφ1
  refine ⟨φ, hφ, hcφ, hsφ, hone_ball, hone_closed, fun x ↦ hvalχ (x - x₀), fun x ↦ ?_⟩
  have hdf := (hχ.differentiable_one (x - x₀)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const x₀)
  simp only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] at hdf
  rw [norm_gradient_eq_norm_fderiv]
  change ‖fderiv ℝ (fun y ↦ χ (y - x₀)) x‖ ≤ _
  rw [hdf.fderiv, ← norm_gradient_eq_norm_fderiv]
  exact hgradχ (x - x₀)

private theorem exists_local_polar_of_open {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω₀ : Set (Space d)}
    (hE : MeasurableSet E) (hΩ₀ : IsOpen Ω₀)
    (μ : Measure (Space d)) [IsLocallyFiniteMeasure μ] (hμΩ₀ : μ Ω₀ ≠ ⊤)
    (hμ : ∀ U, IsOpen U → U ⊆ Ω₀ → μ U = variationalPerimeter b E U) :
    ∃ ν : Space d → Space d,
      (∀ᵐ x ∂μ.restrict Ω₀, ‖ν x‖ = 1) ∧
      ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
        tsupport F ⊆ Ω₀ →
        -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
          ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω₀ := by
  have hP : variationalPerimeter b E Ω₀ ≠ ⊤ := by
    rw [← hμ Ω₀ hΩ₀ Subset.rfl]
    exact hμΩ₀
  obtain ⟨σ, hmass, -, hzero, hdist⟩ :=
    exists_perimeter_vector_measure_concentrated b hE hΩ₀.measurableSet hP
  let : IsFiniteMeasure σ.variation := ⟨by rw [hmass]; exact lt_top_iff_ne_top.mpr hP⟩
  let : IsFiniteMeasure (μ.restrict Ω₀) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact lt_top_iff_ne_top.mpr hμΩ₀⟩
  have hself : σ.variation.restrict Ω₀ = σ.variation :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hzero)
  have heq : μ.restrict Ω₀ = σ.variation := by
    apply Measure.OuterRegular.ext_isOpen
    intro U hU
    calc
      (μ.restrict Ω₀) U = μ (U ∩ Ω₀) := Measure.restrict_apply hU.measurableSet
      _ = variationalPerimeter b E (U ∩ Ω₀) := hμ _ (hU.inter hΩ₀) Set.inter_subset_right
      _ = σ.variation (U ∩ Ω₀) :=
        (variation_eq_variationalPerimeter_of_representation b σ hdist
          (hU.inter hΩ₀) Set.inter_subset_right).symm
      _ = (σ.variation.restrict Ω₀) U := (Measure.restrict_apply hU.measurableSet).symm
      _ = σ.variation U := congrArg (fun m : Measure (Space d) ↦ m U) hself
  have hi := integrable_vectorPolarDensity b σ
  have hn := norm_vectorPolarDensity_ae b σ
  refine ⟨vectorPolarDensity b σ, heq.symm ▸ hn, fun F hF hs ↦ ?_⟩
  rw [heq]
  refine (hdist F hF hs).trans ?_
  nth_rw 1 [← withDensity_vectorPolarDensity b σ]
  exact integral_withDensity_inner_of_ae_bounded hi (hn.mono fun _ h ↦ h.le)
    F.continuous.measurable (norm_nonneg F.toBoundedContinuousFunction)
    F.toBoundedContinuousFunction.norm_coe_le_norm

private theorem integral_symmDiff_cutoff_gradient_le {d : ℕ} {S : Set (Space d)}
    (hS : MeasurableSet S) {x₀ : Space d} {r ε C : ℝ} (_hε : 0 < ε) (_hC : 0 ≤ C)
    {φ : Space d → ℝ} (_hφ : ContDiff ℝ 1 φ)
    (hs : tsupport φ ⊆ ball x₀ (r + ε))
    (hone : ∀ x ∈ ball x₀ r, φ x = 1) (hgrad : ∀ x, ‖gradient φ x‖ ≤ C / ε)
    {G : Space d → Space d} (hunit : ∀ x, ‖G x‖ ≤ 1) :
    (∫ x, S.indicator (fun _ ↦ (1 : ℝ)) x * ‖gradient φ x‖ * ‖G x‖) ≤
      C / ε * volume.real (S ∩ (ball x₀ (r + ε) \ ball x₀ r)) := by
  let A := S ∩ (ball x₀ (r + ε) \ ball x₀ r)
  have hA : MeasurableSet A := hS.inter (measurableSet_ball.diff measurableSet_ball)
  have hAV : volume A ≠ ⊤ := ne_top_of_le_ne_top measure_ball_ne_top
    (measure_mono fun _ hx ↦ hx.2.1)
  have hAi : Integrable (A.indicator (fun _ ↦ C / ε)) volume :=
    (integrableOn_const (C := C / ε) hAV).integrable_indicator hA
  have hpoint (x : Space d) :
      S.indicator (fun _ ↦ (1 : ℝ)) x * ‖gradient φ x‖ * ‖G x‖ ≤
        A.indicator (fun _ ↦ C / ε) x := by
    by_cases hxS : x ∈ S
    · by_cases hxi : x ∈ ball x₀ r
      · have hz := gradient_eq_zero_of_eqOn_open isOpen_ball hone hxi
        simp [A, hxS, hxi, hz]
      · by_cases hxo : x ∈ ball x₀ (r + ε)
        · simp only [indicator_of_mem hxS, one_mul,
            indicator_of_mem (show x ∈ A from ⟨hxS, hxo, hxi⟩)]
          exact (mul_le_mul_of_nonneg_left (hunit x) (norm_nonneg _)).trans
            (by simpa using hgrad x)
        · have hz : gradient φ x = 0 := by
            simp [gradient, fderiv_of_notMem_tsupport ℝ (fun hh ↦ hxo (hs hh))]
          simp [A, hxS, hxo, hz]
    · simp [A, hxS]
  have hle := integral_mono_of_nonneg
    (Eventually.of_forall fun x ↦ mul_nonneg
      (mul_nonneg (by by_cases hx : x ∈ S <;> simp [hx]) (norm_nonneg _)) (norm_nonneg _))
    hAi (Eventually.of_forall hpoint)
  simpa only [integral_indicator_const _ hA, smul_eq_mul, mul_comm (volume.real A)] using hle

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem perimeter_glued_cutoff_test_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {F E Ω₀ : Set (Space d)}
    (hF : MeasurableSet F) (hE : MeasurableSet E)
    (μF₀ μE₀ : Measure (Space d)) [IsFiniteMeasure μF₀] [IsFiniteMeasure μE₀]
    {νF νE : Space d → Space d}
    (hνF : ∀ᵐ x ∂μF₀, ‖νF x‖ = 1) (hνE : ∀ᵐ x ∂μE₀, ‖νE x‖ = 1)
    (hdistF : ∀ H : C_c(Space d, Space d), ContDiff ℝ 1 (H : Space d → Space d) →
      tsupport H ⊆ Ω₀ →
      -(∫ x, F.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b H x) =
        ∫ x, inner ℝ (H x) (νF x) ∂μF₀)
    (hdistE : ∀ H : C_c(Space d, Space d), ContDiff ℝ 1 (H : Space d → Space d) →
      tsupport H ⊆ Ω₀ →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b H x) =
        ∫ x, inner ℝ (H x) (νE x) ∂μE₀)
    {x₀ : Space d} {r ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hsφ : tsupport φ ⊆ ball x₀ (r + ε))
    (hone_ball : ∀ x ∈ ball x₀ r, φ x = 1)
    (hone_closed : ∀ x ∈ closedBall x₀ r, φ x = 1)
    (hval : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hgrad : ∀ x, ‖gradient φ x‖ ≤ C / ε)
    {G : Space d → Space d} (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G)
    (hsG : tsupport G ⊆ Ω₀) (hunit : ∀ x, ‖G x‖ ≤ 1) :
    ‖∫ x, (φ x * F.indicator (fun _ ↦ (1 : ℝ)) x +
      (1 - φ x) * E.indicator (fun _ ↦ (1 : ℝ)) x) * fieldDivergence b G x‖ ≤
      μF₀.real (ball x₀ (r + ε)) + μE₀.real ((closedBall x₀ r)ᶜ) +
        C / ε * volume.real ((symmDiff F E) ∩ (ball x₀ (r + ε) \ ball x₀ r)) := by
  let χF := F.indicator (fun _ : Space d ↦ (1 : ℝ))
  let χE := E.indicator (fun _ : Space d ↦ (1 : ℝ))
  let S := symmDiff F E
  have hS : MeasurableSet S := hF.symmDiff hE
  let ψ : Space d → ℝ := fun x ↦ 1 - φ x
  have hψ : ContDiff ℝ 1 ψ := contDiff_const.sub hφ
  have hψval (x : Space d) : ψ x ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (hval x).2, sub_le_self 1 (hval x).1⟩
  have hgrad_cont : Continuous (gradient φ) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hdc : HasCompactSupport (fieldDivergence b G) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport G)
    intro x hx
    by_contra hnot
    exact hx (fieldDivergence_zero_of_notMem_tsupport b G hnot)
  have hqci : HasCompactSupport (fun x ↦ inner ℝ (gradient φ x) (G x)) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport G)
    intro x hx
    by_contra hnot
    exact hx (by
      change inner ℝ (gradient φ x) (G x) = 0
      rw [image_eq_zero_of_notMem_tsupport hnot, inner_zero_right])
  have hAFi : Integrable (fun x ↦ χF x * φ x * fieldDivergence b G x) := by
    have hi := (hφ.continuous.mul (fieldDivergence_continuous b hG))
      |>.integrable_of_hasCompactSupport (μ := volume) hdc.mul_left
    convert hi.indicator hF using 1
    ext x
    by_cases hx : x ∈ F <;> simp [χF, hx]
  have hAEi : Integrable (fun x ↦ χE x * ψ x * fieldDivergence b G x) := by
    have hi := (hψ.continuous.mul (fieldDivergence_continuous b hG))
      |>.integrable_of_hasCompactSupport (μ := volume) hdc.mul_left
    convert hi.indicator hE using 1
    ext x
    by_cases hx : x ∈ E <;> simp [χE, hx]
  have hQFi : Integrable (fun x ↦ χF x * inner ℝ (gradient φ x) (G x)) := by
    have hi := (hgrad_cont.inner hG.continuous).integrable_of_hasCompactSupport (μ := volume) hqci
    convert hi.indicator hF using 1
    ext x
    by_cases hx : x ∈ F <;> simp [χF, hx]
  have hQEi : Integrable (fun x ↦ χE x * inner ℝ (gradient φ x) (G x)) := by
    have hi := (hgrad_cont.inner hG.continuous).integrable_of_hasCompactSupport (μ := volume) hqci
    convert hi.indicator hE using 1
    ext x
    by_cases hx : x ∈ E <;> simp [χE, hx]
  have hCi : Integrable (fun x ↦ S.indicator (fun _ ↦ (1 : ℝ)) x * ‖gradient φ x‖ * ‖G x‖) := by
    have hi := (hgrad_cont.norm.mul hG.continuous.norm)
      |>.integrable_of_hasCompactSupport (μ := volume) hc.norm.mul_left
    convert hi.indicator hS using 1
    ext x
    by_cases hx : x ∈ S <;> simp [hx]
  have hsub_smul (η : Space d → ℝ) : tsupport (fun x ↦ η x • G x) ⊆ Ω₀ := by
    refine (closure_minimal ?_ (isClosed_tsupport G)).trans hsG
    intro x hx
    by_contra hnot
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hnot])
  let G₁ : C_c(Space d, Space d) :=
    ⟨⟨fun x ↦ φ x • G x, hφ.continuous.smul hG.continuous⟩, hc.smul_left (f := φ)⟩
  let G₂ : C_c(Space d, Space d) :=
    ⟨⟨fun x ↦ ψ x • G x, hψ.continuous.smul hG.continuous⟩, hc.smul_left (f := ψ)⟩
  have hidF := hdistF G₁ (hφ.smul hG) (hsub_smul φ)
  have hidE := hdistE G₂ (hψ.smul hG) (hsub_smul ψ)
  have hdivF (x : Space d) : χF x * fieldDivergence b G₁ x =
      χF x * φ x * fieldDivergence b G x + χF x * inner ℝ (gradient φ x) (G x) := by
    change χF x * fieldDivergence b (fun y ↦ φ y • G y) x = _
    rw [fieldDivergence_fun_smul b (hφ.differentiable_one x) (hG.differentiable_one x)]
    ring
  have hgradψ (x : Space d) : gradient ψ x = -gradient φ x := by
    have hdf := (hasFDerivAt_const (1 : ℝ) x).sub (hφ.differentiable_one x).hasFDerivAt
    change HasFDerivAt ψ (0 - fderiv ℝ φ x) x at hdf
    rw [zero_sub] at hdf
    simp [gradient, hdf.fderiv]
  have hdivE (x : Space d) : χE x * fieldDivergence b G₂ x =
      χE x * ψ x * fieldDivergence b G x - χE x * inner ℝ (gradient φ x) (G x) := by
    change χE x * fieldDivergence b (fun y ↦ ψ y • G y) x = _
    rw [fieldDivergence_fun_smul b (hψ.differentiable_one x) (hG.differentiable_one x),
      hgradψ x, inner_neg_left]
    ring
  change -(∫ x, χF x * fieldDivergence b G₁ x) = _ at hidF
  change -(∫ x, χE x * fieldDivergence b G₂ x) = _ at hidE
  simp_rw [hdivF] at hidF
  simp_rw [hdivE] at hidE
  rw [integral_add hAFi hQFi] at hidF
  rw [integral_sub hAEi hQEi] at hidE
  have hcomb_eq : (∫ x, (φ x * χF x + ψ x * χE x) * fieldDivergence b G x) =
      (∫ x, χF x * φ x * fieldDivergence b G x) +
        ∫ x, χE x * ψ x * fieldDivergence b G x := by
    rw [← integral_add hAFi hAEi]
    congr 1 with x
    ring
  have hgrad_diff : (∫ x, (χF x - χE x) * inner ℝ (gradient φ x) (G x)) =
      (∫ x, χF x * inner ℝ (gradient φ x) (G x)) -
        ∫ x, χE x * inner ℝ (gradient φ x) (G x) := by
    rw [← integral_sub hQFi hQEi]
    congr 1 with x
    ring
  have htotal : (∫ x, (φ x * χF x + ψ x * χE x) * fieldDivergence b G x) =
      -(∫ x, inner ℝ (G₁ x) (νF x) ∂μF₀) -
      (∫ x, inner ℝ (G₂ x) (νE x) ∂μE₀) -
      ∫ x, (χF x - χE x) * inner ℝ (gradient φ x) (G x) := by
    linarith [hidF, hidE, hcomb_eq, hgrad_diff]
  have hφi : Integrable φ μF₀ := Integrable.of_bound hφ.continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x ↦ by rw [Real.norm_of_nonneg (hval x).1]; exact (hval x).2)
  have hψi : Integrable ψ μE₀ := Integrable.of_bound hψ.continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x ↦ by rw [Real.norm_of_nonneg (hψval x).1]; exact (hψval x).2)
  have hnIF : ‖∫ x, inner ℝ (G₁ x) (νF x) ∂μF₀‖ ≤ μF₀.real (ball x₀ (r + ε)) := by
    refine (norm_integral_le_of_norm_le hφi ?_).trans
      (integral_weight_le_measure μF₀ hφ.continuous hval measurableSet_ball
        (fun x hx ↦ image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hsφ hh))))
    filter_upwards [hνF] with x hx
    calc
      ‖inner ℝ (G₁ x) (νF x)‖ ≤ ‖G₁ x‖ * ‖νF x‖ := norm_inner_le_norm _ _
      _ = φ x * ‖G x‖ := by
        change ‖φ x • G x‖ * ‖νF x‖ = _
        rw [norm_smul, Real.norm_of_nonneg (hval x).1, hx, mul_one]
      _ ≤ φ x := by nlinarith [(hval x).1, hunit x]
  have hnIE : ‖∫ x, inner ℝ (G₂ x) (νE x) ∂μE₀‖ ≤ μE₀.real ((closedBall x₀ r)ᶜ) := by
    refine (norm_integral_le_of_norm_le hψi ?_).trans
      (integral_weight_le_measure μE₀ hψ.continuous hψval measurableSet_closedBall.compl
        (fun x hx ↦ by
          have hmem : x ∈ closedBall x₀ r := not_not.mp hx
          simp [ψ, hone_closed x hmem]))
    filter_upwards [hνE] with x hx
    calc
      ‖inner ℝ (G₂ x) (νE x)‖ ≤ ‖G₂ x‖ * ‖νE x‖ := norm_inner_le_norm _ _
      _ = ψ x * ‖G x‖ := by
        change ‖ψ x • G x‖ * ‖νE x‖ = _
        rw [norm_smul, Real.norm_of_nonneg (hψval x).1, hx, mul_one]
      _ ≤ ψ x := by nlinarith [(hψval x).1, hunit x]
  have hnQ : ‖∫ x, (χF x - χE x) * inner ℝ (gradient φ x) (G x)‖ ≤
      C / ε * volume.real (S ∩ (ball x₀ (r + ε) \ ball x₀ r)) := by
    refine (norm_integral_le_of_norm_le hCi ?_).trans
      (integral_symmDiff_cutoff_gradient_le hS hε hC hφ hsφ hone_ball hgrad hunit)
    refine Eventually.of_forall fun x ↦ ?_
    have hdiff_eq : ‖χF x - χE x‖ = S.indicator (fun _ ↦ (1 : ℝ)) x := by
      by_cases hxF : x ∈ F <;> by_cases hxE : x ∈ E <;>
        simp [χF, χE, S, symmDiff, hxF, hxE]
    rw [norm_mul, hdiff_eq]
    have hS0 : 0 ≤ S.indicator (fun _ : Space d ↦ (1 : ℝ)) x := by
      by_cases hx : x ∈ S <;> simp [hx]
    exact (mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) hS0).trans_eq
      (mul_assoc _ _ _).symm
  change ‖∫ x, (φ x * χF x + ψ x * χE x) * fieldDivergence b G x‖ ≤ _
  rw [htotal]
  have htri : ‖-(∫ x, inner ℝ (G₁ x) (νF x) ∂μF₀) -
      (∫ x, inner ℝ (G₂ x) (νE x) ∂μE₀) -
      ∫ x, (χF x - χE x) * inner ℝ (gradient φ x) (G x)‖ ≤
      ‖∫ x, inner ℝ (G₁ x) (νF x) ∂μF₀‖ +
      ‖∫ x, inner ℝ (G₂ x) (νE x) ∂μE₀‖ +
      ‖∫ x, (χF x - χE x) * inner ℝ (gradient φ x) (G x)‖ := by
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ?_ le_rfl
    exact (norm_sub_le _ _).trans (by rw [norm_neg])
  exact htri.trans (add_le_add (add_le_add hnIF hnIE) hnQ)

/-! ### 1. Pointwise derivative ball gluing inequality -/

/-- Any derivative of a monotone function `V : ℝ → ℝ` is nonnegative. -/
theorem monotone_hasDerivAt_nonneg {V : ℝ → ℝ} (hf : Monotone V) {r d' : ℝ}
    (hd : HasDerivAt V d' r) : 0 ≤ d' := by
  refine ge_of_tendsto hd.tendsto_slope_zero_right ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hf (by linarith)))

/-- The `deriv` of a monotone function `V : ℝ → ℝ` is everywhere nonnegative. -/
theorem monotone_deriv_nonneg {V : ℝ → ℝ} (hf : Monotone V) (r : ℝ) :
    0 ≤ deriv V r := by
  by_cases hd : DifferentiableAt ℝ V r
  · exact monotone_hasDerivAt_nonneg hf hd.hasDerivAt
  · simp [deriv_zero_of_not_differentiableAt hd]

/-- Monotonicity of the ball-volume profile `ρ ↦ volume.real (A ∩ ball x₀ ρ)`. -/
theorem monotone_volume_real_inter_ball {d : ℕ} (A : Set (Space d)) (x₀ : Space d) :
    Monotone (fun ρ : ℝ ↦ volume.real (A ∩ ball x₀ ρ)) :=
  fun _ _ hρ ↦ measureReal_mono (inter_subset_inter_right A (ball_subset_ball hρ))

/-- Stronger closed-ball-complement form of `variationalPerimeter_ballGluedSet_le_of_hasDerivAt`. -/
theorem variationalPerimeter_ballGluedSet_le_closedBall_compl_of_hasDerivAt
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {F E Ω : Set (Space d)} (hF : MeasurableSet F) (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μF μE : Measure (Space d)) [IsLocallyFiniteMeasure μF] [IsLocallyFiniteMeasure μE]
    (hμF : ∀ U, IsOpen U → U ⊆ Ω → μF U = variationalPerimeter b F U)
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    {x₀ : Space d} {r d' : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hderiv : HasDerivAt (fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ)) d' r) :
    variationalPerimeter b (ballGluedSet x₀ r F E) Ω ≤
      μF (closedBall x₀ r) + μE (Ω \ closedBall x₀ r) +
        ENNReal.ofReal (ballGluingConstant * d') := by
  let V : ℝ → ℝ := fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ)
  have hV_mono : Monotone V := monotone_volume_real_inter_ball (symmDiff F E) x₀
  have hd'_nonneg : 0 ≤ d' := by
    refine ge_of_tendsto hderiv.tendsto_slope_zero_right ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hV_mono (by linarith)))
  let : Nontrivial (Space d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (M := Space d) (by simp [Space]; omega)
  unfold variationalPerimeter
  refine iSup_le fun G ↦ iSup_le fun hG ↦ iSup_le fun hc ↦
    iSup_le fun hsG ↦ iSup_le fun hunit ↦ ?_
  obtain ⟨δ, hδ, hδΩ⟩ := exists_pos_closedBall_add_subset hΩ hsub
  let K := tsupport G ∪ closedBall x₀ (r + δ)
  have hK : IsCompact K := hc.union (isCompact_closedBall x₀ (r + δ))
  have hKΩ : K ⊆ Ω := union_subset hsG hδΩ
  obtain ⟨N, hKN⟩ := compact_subset_perimeter_ball hK
  let Ω₀ := Ω ∩ ball 0 ((N : ℝ) + 1)
  have hΩ₀ : IsOpen Ω₀ := hΩ.inter isOpen_ball
  have hΩ₀_sub : Ω₀ ⊆ Ω := inter_subset_left
  have hsG₀ : tsupport G ⊆ Ω₀ := subset_union_left.trans (subset_inter hKΩ hKN)
  have hball₀ : closedBall x₀ (r + δ) ⊆ Ω₀ := subset_union_right.trans (subset_inter hKΩ hKN)
  have hμF_lt : μF Ω₀ < ⊤ := (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
  have hμE_lt : μE Ω₀ < ⊤ := (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
  let μF₀ := μF.restrict Ω₀
  let μE₀ := μE.restrict Ω₀
  let : IsFiniteMeasure μF₀ := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact hμF_lt⟩
  let : IsFiniteMeasure μE₀ := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact hμE_lt⟩
  obtain ⟨νF, hνF, hdistF⟩ := exists_local_polar_of_open b hF hΩ₀ μF hμF_lt.ne
    (fun U hU hs ↦ hμF U hU (hs.trans hΩ₀_sub))
  obtain ⟨νE, hνE, hdistE⟩ := exists_local_polar_of_open b hE hΩ₀ μE hμE_lt.ne
    (fun U hU hs ↦ hμE U hU (hs.trans hΩ₀_sub))
  let ε : ℕ → ℝ := fun k ↦ δ * (1 / ((k : ℝ) + 1))
  have hε_pos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hε_le (k : ℕ) : ε k ≤ δ := by
    dsimp [ε]
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := div_le_one (by positivity) |>.mpr (by linarith)
    nlinarith
  have hε_anti : Antitone ε := by
    intro j k hjk
    dsimp [ε]
    refine mul_le_mul_of_nonneg_left ?_ hδ.le
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hε_lim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := δ)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [ε, mul_zero] using hh
  choose φ hφ hcφ hsφ hone_ball hone_closed hval hgrad using
    fun k ↦ exists_translated_ball_cutoff x₀ hr (hε_pos k)
  let χF := F.indicator (fun _ : Space d ↦ (1 : ℝ))
  let χE := E.indicator (fun _ : Space d ↦ (1 : ℝ))
  let χG := (ballGluedSet x₀ r F E).indicator (fun _ : Space d ↦ (1 : ℝ))
  let w : ℕ → Space d → ℝ := fun k x ↦ φ k x * χF x + (1 - φ k x) * χE x
  have hdiv_cont := fieldDivergence_continuous b hG
  have hdc : HasCompactSupport (fieldDivergence b G) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport G)
    intro x hx
    by_contra hnot
    exact hx (fieldDivergence_zero_of_notMem_tsupport b G hnot)
  have h_lhs_lim : Tendsto (fun k ↦ ‖∫ x, w k x * fieldDivergence b G x‖) atTop
      (𝓝 ‖∫ x, χG x * fieldDivergence b G x‖) := by
    apply Tendsto.norm
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖fieldDivergence b G x‖)
    · intro k
      have hwm : Measurable (w k) :=
        ((hφ k).continuous.measurable.mul (measurable_const.indicator hF)).add
          ((measurable_const.sub (hφ k).continuous.measurable).mul (measurable_const.indicator hE))
      exact (hwm.aestronglyMeasurable.mul hdiv_cont.aestronglyMeasurable)
    · exact hdiv_cont.norm.integrable_of_hasCompactSupport hdc.norm
    · intro k
      refine Eventually.of_forall fun x ↦ ?_
      have hχF : χF x ∈ Icc (0 : ℝ) 1 := by by_cases hx : x ∈ F <;> simp [χF, hx]
      have hχE : χE x ∈ Icc (0 : ℝ) 1 := by by_cases hx : x ∈ E <;> simp [χE, hx]
      have hw0 : 0 ≤ w k x := add_nonneg (mul_nonneg (hval k x).1 hχF.1)
        (mul_nonneg (sub_nonneg.mpr (hval k x).2) hχE.1)
      have hw1 : w k x ≤ 1 := by
        calc
          w k x ≤ φ k x * 1 + (1 - φ k x) * 1 := add_le_add
            (mul_le_mul_of_nonneg_left hχF.2 (hval k x).1)
            (mul_le_mul_of_nonneg_left hχE.2 (sub_nonneg.mpr (hval k x).2))
          _ = 1 := by ring
      rw [norm_mul, Real.norm_of_nonneg hw0]
      exact mul_le_of_le_one_left (norm_nonneg _) hw1
    · have hsphere0 : volume (sphere x₀ r) = 0 := volume.addHaar_sphere x₀ r
      filter_upwards [compl_mem_ae_iff.mpr hsphere0] with x hx_not_sphere
      have hne : dist x x₀ ≠ r := fun hh ↦ hx_not_sphere (mem_sphere.mpr hh)
      rcases hne.lt_or_gt with hlt | hgt
      · have hx_ball : x ∈ ball x₀ r := hlt
        have heq (k : ℕ) : w k x = χG x := by
          have hφ1 := hone_ball k x hx_ball
          by_cases hxF : x ∈ F <;>
            simp [w, χF, χE, χG, hφ1, hxF, mem_ballGluedSet_of_mem_ball hx_ball]
        simp_rw [heq]
        exact tendsto_const_nhds
      · have hx_not_ball : x ∉ ball x₀ r := not_lt.mpr hgt.le
        have hev : (fun k ↦ w k x * fieldDivergence b G x) =ᶠ[atTop]
            fun _ ↦ χG x * fieldDivergence b G x := by
          filter_upwards [hε_lim.eventually (gt_mem_nhds (sub_pos.mpr hgt))] with k hk
          have hx_out : x ∉ ball x₀ (r + ε k) := by
            rw [mem_ball, not_lt]
            linarith
          have hφ0 : φ k x = 0 :=
            image_eq_zero_of_notMem_tsupport (fun hh ↦ hx_out (hsφ k hh))
          by_cases hxE : x ∈ E <;>
            simp [w, χF, χE, χG, hφ0, hxE, mem_ballGluedSet_of_notMem_ball hx_not_ball]
        exact tendsto_const_nhds.congr' hev.symm
  have h_muF_lim : Tendsto (fun k ↦ μF₀.real (ball x₀ (r + ε k))) atTop
      (𝓝 (μF.real (closedBall x₀ r))) := by
    have heq_res (k : ℕ) : μF₀ (ball x₀ (r + ε k)) = μF (ball x₀ (r + ε k)) := by
      rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr]
      exact (ball_subset_closedBall.trans (closedBall_subset_closedBall
        (by linarith [hε_le k]))).trans hball₀
    have hinter_eq : (⋂ k : ℕ, ball x₀ (r + ε k)) = closedBall x₀ r := by
      ext x
      simp only [mem_iInter, mem_ball, mem_closedBall]
      refine ⟨fun hx ↦ ?_, fun hx k ↦ hx.trans_lt (lt_add_of_pos_right r (hε_pos k))⟩
      have hlim : Tendsto (fun k ↦ r + ε k) atTop (𝓝 r) := by
        simpa only [add_zero] using (tendsto_const_nhds (x := r)).add hε_lim
      exact ge_of_tendsto hlim (Eventually.of_forall fun k ↦ (hx k).le)
    have hlim_enn : Tendsto (fun k ↦ μF (ball x₀ (r + ε k))) atTop
        (𝓝 (μF (closedBall x₀ r))) := by
      rw [← hinter_eq]
      refine tendsto_measure_iInter_atTop (fun _ ↦ measurableSet_ball.nullMeasurableSet)
        (fun j k hjk ↦ ball_subset_ball (by linarith [hε_anti hjk])) ⟨0, ?_⟩
      exact ne_top_of_le_ne_top hμF_lt.ne
        (measure_mono ((ball_subset_closedBall.trans (closedBall_subset_closedBall
          (by linarith [hε_le 0]))).trans hball₀))
    have hclosed_ne_top : μF (closedBall x₀ r) ≠ ⊤ :=
      (isCompact_closedBall x₀ r).measure_ne_top
    have htoReal := (ENNReal.tendsto_toReal hclosed_ne_top).comp hlim_enn
    refine htoReal.congr fun k ↦ ?_
    simp [Measure.real, heq_res k]
  have h_slope_lim : Tendsto (fun k ↦ ballGluingConstant / ε k *
      volume.real ((symmDiff F E) ∩ (ball x₀ (r + ε k) \ ball x₀ r))) atTop
      (𝓝 (ballGluingConstant * d')) := by
    have hε_nhds : Tendsto ε atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ε hε_lim
        (Eventually.of_forall fun k ↦ (hε_pos k).ne')
    have hslope := (hderiv.tendsto_slope_zero.comp hε_nhds).const_mul ballGluingConstant
    refine hslope.congr fun k ↦ ?_
    simp only [Function.comp_def, smul_eq_mul]
    have hset : (symmDiff F E) ∩ (ball x₀ (r + ε k) \ ball x₀ r) =
        ((symmDiff F E) ∩ ball x₀ (r + ε k)) \ ((symmDiff F E) ∩ ball x₀ r) := by
      ext x
      simp only [mem_inter_iff, Set.mem_sdiff]
      tauto
    have hsdiff : volume.real ((symmDiff F E) ∩ (ball x₀ (r + ε k) \ ball x₀ r)) =
        V (r + ε k) - V r := by
      rw [hset, measureReal_sdiff]
      · exact inter_subset_inter_right _ (ball_subset_ball (by linarith [hε_pos k]))
      · exact (hF.symmDiff hE).inter measurableSet_ball
    rw [hsdiff]
    ring
  have h_rhs_lim : Tendsto (fun k ↦ μF₀.real (ball x₀ (r + ε k)) +
      μE₀.real ((closedBall x₀ r)ᶜ) +
      ballGluingConstant / ε k *
        volume.real ((symmDiff F E) ∩ (ball x₀ (r + ε k) \ ball x₀ r))) atTop
      (𝓝 (μF.real (closedBall x₀ r) + μE₀.real ((closedBall x₀ r)ᶜ) +
        ballGluingConstant * d')) :=
    (h_muF_lim.add tendsto_const_nhds).add h_slope_lim
  have hbound_real : ‖∫ x, χG x * fieldDivergence b G x‖ ≤
      μF.real (closedBall x₀ r) + μE₀.real ((closedBall x₀ r)ᶜ) +
        ballGluingConstant * d' := by
    refine le_of_tendsto_of_tendsto h_lhs_lim h_rhs_lim (Eventually.of_forall fun k ↦ ?_)
    exact perimeter_glued_cutoff_test_bound b hF hE μF₀ μE₀ hνF hνE hdistF hdistE
      (hε_pos k) ballGluingConstant_pos.le (hφ k) (hsφ k) (hone_ball k) (hone_closed k)
      (hval k) (hgrad k) hG hc hsG₀ hunit
  have h_ofReal := ENNReal.ofReal_le_ofReal hbound_real
  rw [ENNReal.ofReal_add (add_nonneg measureReal_nonneg measureReal_nonneg)
      (mul_nonneg ballGluingConstant_pos.le hd'_nonneg),
    ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg] at h_ofReal
  have hF_eq : ENNReal.ofReal (μF.real (closedBall x₀ r)) = μF (closedBall x₀ r) :=
    ENNReal.ofReal_toReal (isCompact_closedBall x₀ r).measure_ne_top
  have hE_le : ENNReal.ofReal (μE₀.real ((closedBall x₀ r)ᶜ)) ≤ μE (Ω \ closedBall x₀ r) := by
    rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μE₀ _),
      Measure.restrict_apply measurableSet_closedBall.compl]
    exact measure_mono fun x hx ↦ ⟨hΩ₀_sub hx.2, hx.1⟩
  rw [hF_eq] at h_ofReal
  exact h_ofReal.trans (add_le_add (add_le_add le_rfl hE_le) le_rfl)

/-- Ball gluing bound at a radius where the symmetric-difference ball volume is differentiable. -/
theorem variationalPerimeter_ballGluedSet_le_of_hasDerivAt
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {F E Ω : Set (Space d)} (hF : MeasurableSet F) (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μF μE : Measure (Space d)) [IsLocallyFiniteMeasure μF] [IsLocallyFiniteMeasure μE]
    (hμF : ∀ U, IsOpen U → U ⊆ Ω → μF U = variationalPerimeter b F U)
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    {x₀ : Space d} {r d' : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hderiv : HasDerivAt (fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ)) d' r) :
    variationalPerimeter b (ballGluedSet x₀ r F E) Ω ≤
      μF (closedBall x₀ r) + μE (Ω \ ball x₀ r) +
        ENNReal.ofReal (ballGluingConstant * d') := by
  refine (variationalPerimeter_ballGluedSet_le_closedBall_compl_of_hasDerivAt
    hd b hF hE hΩ μF μE hμF hμE hr hsub hderiv).trans ?_
  refine add_le_add (add_le_add le_rfl ?_) le_rfl
  exact measure_mono fun _ hx ↦ ⟨hx.1, fun h ↦ hx.2 (ball_subset_closedBall h)⟩

/-! ### 2. Countability of spheres carrying positive Radon mass -/

/-- For any locally finite (in particular, finite) measure `ν` on `Space d`, only countably many
positive radii have spheres carrying nonzero `ν`-mass. -/
theorem countable_spheres_positive_measure {d : ℕ} (ν : Measure (Space d))
    [IsLocallyFiniteMeasure ν] (x₀ : Space d) :
    {r : ℝ | 0 < r ∧ ν (sphere x₀ r) ≠ 0}.Countable := by
  let S : ℕ → ℕ → Set ℝ := fun N M ↦
    {r : ℝ | 0 < r ∧ r ≤ (N : ℝ) ∧ 1 / ((M : ℝ) + 1) ≤ ν.real (sphere x₀ r)}
  have hsub : {r : ℝ | 0 < r ∧ ν (sphere x₀ r) ≠ 0} ⊆ ⋃ N : ℕ, ⋃ M : ℕ, S N M := by
    intro r ⟨hr, hνr⟩
    obtain ⟨N, hN⟩ := exists_nat_ge r
    have hpos : 0 < ν.real (sphere x₀ r) :=
      ENNReal.toReal_pos hνr (isCompact_sphere x₀ r).measure_ne_top
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt hpos
    exact mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨M, hr, hN, hM.le⟩⟩
  refine Countable.mono hsub (countable_iUnion fun N ↦ countable_iUnion fun M ↦ ?_)
  apply Set.Finite.countable
  by_contra hnot
  have hinf : (S N M).Infinite := hnot
  let B := ν.real (closedBall x₀ (N : ℝ))
  let K := ⌈B * ((M : ℝ) + 1)⌉₊ + 1
  obtain ⟨t, htS, hcard⟩ := hinf.exists_subset_card_eq K
  have hdisj : PairwiseDisjoint (t : Set ℝ) (fun r ↦ sphere x₀ r) := by
    intro r₁ _ r₂ _ hne
    exact disjoint_left.mpr fun x hx₁ hx₂ ↦
      hne ((mem_sphere.mp hx₁).symm.trans (mem_sphere.mp hx₂))
  have hsum_enn : (∑ r ∈ t, ν (sphere x₀ r)) ≤ ν (closedBall x₀ (N : ℝ)) := by
    rw [← measure_biUnion_finset hdisj (fun _ _ ↦ isClosed_sphere.measurableSet)]
    refine measure_mono ?_
    intro x hx
    obtain ⟨r, hrt, hxr⟩ := mem_iUnion₂.mp hx
    rw [mem_closedBall, mem_sphere.mp hxr]
    exact (htS hrt).2.1
  have hsum_real : (∑ r ∈ t, ν.real (sphere x₀ r)) ≤ B := by
    have heq : (∑ r ∈ t, ν.real (sphere x₀ r)) = (∑ r ∈ t, ν (sphere x₀ r)).toReal := by
      simp only [Measure.real]
      exact (ENNReal.toReal_sum fun r _ ↦ (isCompact_sphere x₀ r).measure_ne_top).symm
    rw [heq]
    exact ENNReal.toReal_mono (isCompact_closedBall x₀ (N : ℝ)).measure_ne_top hsum_enn
  have hlow : (K : ℝ) * (1 / ((M : ℝ) + 1)) ≤ ∑ r ∈ t, ν.real (sphere x₀ r) := by
    calc
      (K : ℝ) * (1 / ((M : ℝ) + 1)) = ∑ _r ∈ t, (1 / ((M : ℝ) + 1)) := by
        simp [hcard, nsmul_eq_mul]
      _ ≤ ∑ r ∈ t, ν.real (sphere x₀ r) := Finset.sum_le_sum fun r hr ↦ (htS hr).2.2
  have hMpos : 0 < (M : ℝ) + 1 := by positivity
  have hK_le : (K : ℝ) ≤ B * ((M : ℝ) + 1) := by
    have hh := mul_le_mul_of_nonneg_right (hlow.trans hsum_real) hMpos.le
    have hsimp : (K : ℝ) * (1 / ((M : ℝ) + 1)) * ((M : ℝ) + 1) = (K : ℝ) := by field_simp
    rwa [hsimp] at hh
  have hceil : B * ((M : ℝ) + 1) ≤ (⌈B * ((M : ℝ) + 1)⌉₊ : ℝ) := Nat.le_ceil _
  have hK_def : (K : ℝ) = (⌈B * ((M : ℝ) + 1)⌉₊ : ℝ) + 1 := by simp [K]
  linarith

/-- Positive radii whose spheres have nonzero `ν`-mass form a Lebesgue-null set. -/
theorem volume_spheres_positive_measure_eq_zero {d : ℕ} (ν : Measure (Space d))
    [IsLocallyFiniteMeasure ν] (x₀ : Space d) :
    volume {r : ℝ | 0 < r ∧ ν (sphere x₀ r) ≠ 0} = 0 :=
  (countable_spheres_positive_measure ν x₀).measure_zero volume

/-- For Lebesgue-a.e. positive radius `r`, the sphere `sphere x₀ r` has zero `ν`-mass. -/
theorem ae_sphere_measure_eq_zero {d : ℕ} (ν : Measure (Space d))
    [IsLocallyFiniteMeasure ν] (x₀ : Space d) :
    ∀ᵐ r : ℝ ∂volume, 0 < r → ν (sphere x₀ r) = 0 := by
  have hnull := volume_spheres_positive_measure_eq_zero ν x₀
  filter_upwards [compl_mem_ae_iff.mpr hnull] with r hr hrpos
  by_contra hne
  exact hr ⟨hrpos, hne⟩

/-! ### 3. Almost-everywhere good gluing radii -/

/-- For Lebesgue-a.e. radius `r ∈ Ioo 0 R` (`ball x₀ R ⊆ Ω`), neither perimeter measure charges
`sphere x₀ r`, the symmetric-difference volume profile is differentiable at `r`, and the sharp
ball-gluing perimeter inequality holds without boundary sphere atoms. -/
theorem ae_radius_ballGluedSet_perimeter_le {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {F E Ω : Set (Space d)} (hF : MeasurableSet F) (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μF μE : Measure (Space d)) [IsLocallyFiniteMeasure μF] [IsLocallyFiniteMeasure μE]
    (hμF : ∀ U, IsOpen U → U ⊆ Ω → μF U = variationalPerimeter b F U)
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    (x₀ : Space d) {R : ℝ} (hsub : ball x₀ R ⊆ Ω) :
    ∀ᵐ r : ℝ ∂volume, r ∈ Ioo 0 R →
      μF (sphere x₀ r) = 0 ∧
      μE (sphere x₀ r) = 0 ∧
      HasDerivAt (fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ))
        (deriv (fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ)) r) r ∧
      variationalPerimeter b (ballGluedSet x₀ r F E) Ω ≤
        μF (ball x₀ r) + μE (Ω \ closedBall x₀ r) +
          ENNReal.ofReal (ballGluingConstant *
            deriv (fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ)) r) := by
  let V : ℝ → ℝ := fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ)
  have hV_mono : Monotone V := monotone_volume_real_inter_ball (symmDiff F E) x₀
  filter_upwards [ae_sphere_measure_eq_zero μF x₀, ae_sphere_measure_eq_zero μE x₀,
    hV_mono.ae_hasDerivAt] with r hF0 hE0 hdV hr
  have hrpos : 0 < r := hr.1
  have hF_sph : μF (sphere x₀ r) = 0 := hF0 hrpos
  have hE_sph : μE (sphere x₀ r) = 0 := hE0 hrpos
  have hdV' : HasDerivAt V (deriv V r) r := hdV.deriv ▸ hdV
  have hclosed_sub : closedBall x₀ r ⊆ Ω := (closedBall_subset_ball hr.2).trans hsub
  have hperim := variationalPerimeter_ballGluedSet_le_closedBall_compl_of_hasDerivAt
    hd b hF hE hΩ μF μE hμF hμE hrpos hclosed_sub hdV'
  have hclosed_eq : μF (closedBall x₀ r) = μF (ball x₀ r) := by
    apply le_antisymm _ (measure_mono ball_subset_closedBall)
    have hcov : closedBall x₀ r ⊆ ball x₀ r ∪ sphere x₀ r := by
      intro x hx
      rcases (mem_closedBall.mp hx).lt_or_eq with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq
    calc
      μF (closedBall x₀ r) ≤ μF (ball x₀ r ∪ sphere x₀ r) := measure_mono hcov
      _ ≤ μF (ball x₀ r) + μF (sphere x₀ r) := measure_union_le _ _
      _ = μF (ball x₀ r) := by rw [hF_sph, add_zero]
  rw [hclosed_eq] at hperim
  exact ⟨hF_sph, hE_sph, hdV', hperim⟩

/-! ### 4. Monotone derivative integration and good-radius selection -/

/-- For any monotone function `V : ℝ → ℝ`, its derivative is integrable on every bounded open
interval `Ioo a b` and satisfies `∫ r in Ioo a b, deriv V r ≤ V b - V a`. -/
theorem monotone_setIntegral_deriv_Ioo_le {V : ℝ → ℝ} (hf : Monotone V)
    {a b : ℝ} (hab : a ≤ b) :
    IntegrableOn (deriv V) (Ioo a b) volume ∧
      (∫ r in Ioo a b, deriv V r) ≤ V b - V a := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  let μ := hf.stieltjesFunction.measure
  let g : ℝ → ℝ := fun r ↦ (μ.rnDeriv volume r).toReal
  have hμ_ne_top : μ (Ioo a b) ≠ ⊤ := by
    rw [StieltjesFunction.measure_Ioo]
    exact ENNReal.ofReal_ne_top
  have hg_int : IntegrableOn g (Ioo a b) volume :=
    Measure.integrableOn_toReal_rnDeriv hμ_ne_top
  have hae_eq : deriv V =ᵐ[volume] g := by
    filter_upwards [hf.ae_hasDerivAt] with r hr
    exact hr.deriv
  have hderiv_int : IntegrableOn (deriv V) (Ioo a b) volume :=
    hg_int.congr_fun_ae (ae_restrict_of_ae hae_eq.symm)
  have hleftLim_le : Function.leftLim hf.stieltjesFunction b ≤ V b := by
    refine le_of_tendsto (hf.stieltjesFunction.mono.tendsto_leftLim b) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < b)
    obtain ⟨z, hyz, hzb⟩ := exists_between hy
    rw [hf.stieltjesFunction_eq]
    exact (hf.rightLim_le hyz).trans (hf hzb.le)
  have ha_le : V a ≤ hf.stieltjesFunction a := by
    rw [hf.stieltjesFunction_eq]
    exact hf.le_rightLim le_rfl
  have hdiff_le : Function.leftLim hf.stieltjesFunction b - hf.stieltjesFunction a ≤ V b - V a :=
    sub_le_sub hleftLim_le ha_le
  have h_enn : ENNReal.ofReal (∫ r in Ioo a b, g r) ≤ ENNReal.ofReal (V b - V a) := by
    rw [ofReal_integral_eq_lintegral_ofReal hg_int (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)]
    calc
      (∫⁻ r in Ioo a b, ENNReal.ofReal (g r) ∂volume) ≤
          ∫⁻ r in Ioo a b, μ.rnDeriv volume r ∂volume :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_toReal_le
      _ ≤ μ (Ioo a b) := Measure.setLIntegral_rnDeriv_le (Ioo a b)
      _ = ENNReal.ofReal (Function.leftLim hf.stieltjesFunction b - hf.stieltjesFunction a) :=
        hf.stieltjesFunction.measure_Ioo
      _ ≤ ENNReal.ofReal (V b - V a) := ENNReal.ofReal_le_ofReal hdiff_le
  have hg_le : (∫ r in Ioo a b, g r) ≤ V b - V a :=
    (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr (hf hab))).mp h_enn
  refine ⟨hderiv_int, ?_⟩
  rwa [integral_congr_ae (ae_restrict_of_ae hae_eq)]

/-- Mean-value radius selection for ball gluing: on any open radius interval `Ioo a r_hi` with
`0 < a < r_hi` and `ball x₀ r_hi ⊆ Ω`, there exists a good gluing radius whose radial volume
derivative is bounded by the annular symmetric-difference volume divided by `r_hi - a`. -/
theorem exists_radius_ballGluedSet_perimeter_le {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {F E Ω : Set (Space d)} (hF : MeasurableSet F) (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μF μE : Measure (Space d)) [IsLocallyFiniteMeasure μF] [IsLocallyFiniteMeasure μE]
    (hμF : ∀ U, IsOpen U → U ⊆ Ω → μF U = variationalPerimeter b F U)
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    (x₀ : Space d) {a r_hi : ℝ} (ha : 0 < a) (har : a < r_hi) (hsub : ball x₀ r_hi ⊆ Ω) :
    ∃ r ∈ Ioo a r_hi,
      μF (sphere x₀ r) = 0 ∧
      μE (sphere x₀ r) = 0 ∧
      HasDerivAt (fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ))
        (deriv (fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ)) r) r ∧
      deriv (fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ)) r ≤
        volume.real ((symmDiff F E) ∩ (ball x₀ r_hi \ ball x₀ a)) / (r_hi - a) ∧
      variationalPerimeter b (ballGluedSet x₀ r F E) Ω ≤
        μF (ball x₀ r) + μE (Ω \ closedBall x₀ r) +
          ENNReal.ofReal (ballGluingConstant *
            deriv (fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ)) r) := by
  let V : ℝ → ℝ := fun ρ ↦ volume.real ((symmDiff F E) ∩ ball x₀ ρ)
  have hV_mono : Monotone V := monotone_volume_real_inter_ball (symmDiff F E) x₀
  obtain ⟨hderiv_int, hint_le⟩ := monotone_setIntegral_deriv_Ioo_le hV_mono har.le
  have hann : V r_hi - V a = volume.real ((symmDiff F E) ∩ (ball x₀ r_hi \ ball x₀ a)) := by
    have hset : (symmDiff F E) ∩ (ball x₀ r_hi \ ball x₀ a) =
        ((symmDiff F E) ∩ ball x₀ r_hi) \ ((symmDiff F E) ∩ ball x₀ a) := by
      ext x
      simp only [mem_inter_iff, Set.mem_sdiff]
      tauto
    rw [hset, measureReal_sdiff]
    · exact inter_subset_inter_right _ (ball_subset_ball har.le)
    · exact (hF.symmDiff hE).inter measurableSet_ball
  let M := (V r_hi - V a) / (r_hi - a)
  have hae_good := ae_radius_ballGluedSet_perimeter_le hd b hF hE hΩ μF μE hμF hμE x₀ hsub
  have hae_res : ∀ᵐ r : ℝ ∂volume.restrict (Ioo a r_hi),
      μF (sphere x₀ r) = 0 ∧
      μE (sphere x₀ r) = 0 ∧
      HasDerivAt V (deriv V r) r ∧
      variationalPerimeter b (ballGluedSet x₀ r F E) Ω ≤
        μF (ball x₀ r) + μE (Ω \ closedBall x₀ r) +
          ENNReal.ofReal (ballGluingConstant * deriv V r) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae_good] with r hr hmem
    exact hr ⟨ha.trans hmem.1, hmem.2⟩
  by_contra hnone
  push Not at hnone
  have hae_gt : ∀ᵐ r : ℝ ∂volume.restrict (Ioo a r_hi), M < deriv V r := by
    filter_upwards [hae_res, ae_restrict_mem measurableSet_Ioo] with r hgood hmem
    have hh := hnone r hmem hgood.1 hgood.2.1 hgood.2.2.1
    by_contra hle
    push Not at hle
    have hM : deriv V r ≤ volume.real ((symmDiff F E) ∩ (ball x₀ r_hi \ ball x₀ a)) / (r_hi - a) := by
      rwa [← hann]
    exact not_le_of_gt (hh hM) hgood.2.2.2
  have hae_le : (fun _ : ℝ ↦ M) ≤ᵐ[volume.restrict (Ioo a r_hi)] deriv V :=
    hae_gt.mono fun _ hr ↦ hr.le
  have hIoo_ne_top : volume (Ioo a r_hi) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hM_int : IntegrableOn (fun _ : ℝ ↦ M) (Ioo a r_hi) volume :=
    integrableOn_const hIoo_ne_top
  have hconst_int : (∫ _r in Ioo a r_hi, M) = V r_hi - V a := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_pos.mpr har).le]
    dsimp [M]
    field_simp [(sub_pos.mpr har).ne']
  have hint_eq : (∫ _r in Ioo a r_hi, M) = ∫ r in Ioo a r_hi, deriv V r := by
    apply le_antisymm
    · exact integral_mono_ae hM_int hderiv_int hae_le
    · linarith [hconst_int, hint_le]
  have hae_eq : (fun _ : ℝ ↦ M) =ᵐ[volume.restrict (Ioo a r_hi)] deriv V :=
    (integral_eq_iff_of_ae_le hM_int hderiv_int hae_le).mp hint_eq
  have hae_false : ∀ᵐ _r : ℝ ∂volume.restrict (Ioo a r_hi), False := by
    filter_upwards [hae_gt, hae_eq] with r hgt heq
    exact hgt.ne heq
  rw [ae_iff] at hae_false
  have hzero : (volume.restrict (Ioo a r_hi)) univ = 0 := by
    simpa using hae_false
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo] at hzero
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr har)).ne' hzero

/-! ### 5. Specializations to bounded ball truncation and ball deletion -/

/-- A set contained in `ball x₀ r` (`closedBall x₀ r ⊆ Ω`, `IsOpen Ω`, `0 < r`) has the same
variational perimeter in `univ` as in `Ω`. -/
theorem variationalPerimeter_subset_ball_eq_univ {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {A Ω : Set (Space d)}
    {x₀ : Space d} {r : ℝ} (hr : 0 < r) (hA : A ⊆ ball x₀ r)
    (hΩ : IsOpen Ω) (hsub : closedBall x₀ r ⊆ Ω) :
    variationalPerimeter b A univ = variationalPerimeter b A Ω := by
  apply le_antisymm _ (variationalPerimeter_mono b A (subset_univ _))
  obtain ⟨δ, hδ, hδΩ⟩ := exists_pos_closedBall_add_subset hΩ hsub
  obtain ⟨η, hη, _, hsη, hone_ball, _, hvalη, _⟩ :=
    exists_translated_ball_cutoff x₀ (r := r + δ / 2) (ε := δ / 2) (by linarith) (by positivity)
  unfold variationalPerimeter
  refine iSup_le fun G ↦ iSup_le fun hG ↦ iSup_le fun hc ↦
    iSup_le fun _ ↦ iSup_le fun hunit ↦ ?_
  let G' : Space d → Space d := fun x ↦ η x • G x
  have hG' : ContDiff ℝ 1 G' := hη.smul hG
  have hc' : HasCompactSupport G' := hc.smul_left (f := η)
  have hs' : tsupport G' ⊆ Ω := by
    have h1 : tsupport G' ⊆ tsupport η := by
      refine closure_minimal ?_ (isClosed_tsupport η)
      intro x hx
      by_contra hnot
      exact hx (by simp [G', image_eq_zero_of_notMem_tsupport hnot])
    refine h1.trans (hsη.trans ?_)
    have heq : r + δ / 2 + δ / 2 = r + δ := by ring
    rw [heq]
    exact ball_subset_closedBall.trans hδΩ
  have hunit' (x : Space d) : ‖G' x‖ ≤ 1 := by
    dsimp [G']
    rw [norm_smul, Real.norm_of_nonneg (hvalη x).1]
    nlinarith [(hvalη x).1, (hvalη x).2, hunit x]
  have hint_eq : (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x) =
      ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G' x := by
    congr 1 with x
    by_cases hxA : x ∈ A
    · have hx_in : x ∈ ball x₀ (r + δ / 2) :=
        (ball_subset_ball (by linarith)) (hA hxA)
      have hev : G' =ᶠ[𝓝 x] G := by
        filter_upwards [isOpen_ball.mem_nhds hx_in] with y hy
        simp [G', hone_ball y hy]
      simp [hxA, fieldDivergence, hev.fderiv_eq]
    · simp [hxA]
  rw [hint_eq]
  exact le_iSup_of_le G' (le_iSup_of_le hG' (le_iSup_of_le hc'
    (le_iSup_of_le hs' (le_iSup_of_le hunit' le_rfl))))

/-- Pointwise derivative global perimeter bound for the bounded ball truncation `E ∩ ball x₀ r`. -/
theorem variationalPerimeter_inter_ball_univ_le_of_hasDerivAt
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μE : Measure (Space d)) [IsLocallyFiniteMeasure μE]
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    {x₀ : Space d} {r d' : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hderiv : HasDerivAt (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) d' r) :
    variationalPerimeter b (E ∩ ball x₀ r) univ ≤
      μE (closedBall x₀ r) + ENNReal.ofReal (ballGluingConstant * d') := by
  rw [variationalPerimeter_subset_ball_eq_univ b hr inter_subset_right hΩ hsub,
    ← ballGluedSet_empty_right]
  have hsymm : symmDiff E (∅ : Set (Space d)) = E := by ext x; simp [symmDiff]
  have hd' : HasDerivAt (fun ρ ↦ volume.real ((symmDiff E ∅) ∩ ball x₀ ρ)) d' r := by
    rwa [hsymm]
  have hbound := variationalPerimeter_ballGluedSet_le_of_hasDerivAt hd b hE MeasurableSet.empty hΩ
    μE (0 : Measure (Space d)) hμE (fun U _ _ ↦ by simp) hr hsub hd'
  simpa using hbound

/-- For Lebesgue-a.e. radius `r ∈ Ioo 0 R` (`ball x₀ R ⊆ Ω`), the bounded ball truncation
`E ∩ ball x₀ r` has global perimeter bounded by `μE (ball x₀ r) + C * deriv V_E r`. -/
theorem ae_radius_inter_ball_univ_perimeter_le {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μE : Measure (Space d)) [IsLocallyFiniteMeasure μE]
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    (x₀ : Space d) {R : ℝ} (hsub : ball x₀ R ⊆ Ω) :
    ∀ᵐ r : ℝ ∂volume, r ∈ Ioo 0 R →
      μE (sphere x₀ r) = 0 ∧
      HasDerivAt (fun ρ ↦ volume.real (E ∩ ball x₀ ρ))
        (deriv (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) r) r ∧
      variationalPerimeter b (E ∩ ball x₀ r) univ ≤
        μE (ball x₀ r) +
          ENNReal.ofReal (ballGluingConstant *
            deriv (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) r) := by
  have hsymm : symmDiff E (∅ : Set (Space d)) = E := by ext x; simp [symmDiff]
  have hae := ae_radius_ballGluedSet_perimeter_le hd b hE MeasurableSet.empty hΩ
    μE (0 : Measure (Space d)) hμE (fun U _ _ ↦ by simp) x₀ hsub
  simp only [hsymm, ballGluedSet_empty_right, Measure.coe_zero, Pi.zero_apply, add_zero] at hae
  filter_upwards [hae] with r hr hmem
  obtain ⟨hsph, -, hdV, hperim⟩ := hr hmem
  rw [← variationalPerimeter_subset_ball_eq_univ b hmem.1 inter_subset_right hΩ
    ((closedBall_subset_ball hmem.2).trans hsub)] at hperim
  exact ⟨hsph, hdV, hperim⟩

/-- Mean-value radius selection for bounded ball truncation `E ∩ ball x₀ r` in `univ`. -/
theorem exists_radius_inter_ball_univ_perimeter_le {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μE : Measure (Space d)) [IsLocallyFiniteMeasure μE]
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    (x₀ : Space d) {a r_hi : ℝ} (ha : 0 < a) (har : a < r_hi) (hsub : ball x₀ r_hi ⊆ Ω) :
    ∃ r ∈ Ioo a r_hi,
      μE (sphere x₀ r) = 0 ∧
      HasDerivAt (fun ρ ↦ volume.real (E ∩ ball x₀ ρ))
        (deriv (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) r) r ∧
      deriv (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) r ≤
        volume.real (E ∩ (ball x₀ r_hi \ ball x₀ a)) / (r_hi - a) ∧
      variationalPerimeter b (E ∩ ball x₀ r) univ ≤
        μE (ball x₀ r) +
          ENNReal.ofReal (ballGluingConstant *
            deriv (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) r) := by
  have hsymm : symmDiff E (∅ : Set (Space d)) = E := by ext x; simp [symmDiff]
  obtain ⟨r, hr, hsph, -, hdV, hM, hperim⟩ :=
    exists_radius_ballGluedSet_perimeter_le hd b hE MeasurableSet.empty hΩ
      μE (0 : Measure (Space d)) hμE (fun U _ _ ↦ by simp) x₀ ha har hsub
  simp only [hsymm, ballGluedSet_empty_right, Measure.coe_zero, Pi.zero_apply, add_zero]
    at hdV hM hperim
  rw [← variationalPerimeter_subset_ball_eq_univ b (ha.trans hr.1) inter_subset_right hΩ
    ((closedBall_subset_ball hr.2).trans hsub)] at hperim
  exact ⟨r, hr, hsph, hdV, hM, hperim⟩

/-- Pointwise derivative perimeter bound for the ball deletion competitor `E \ ball x₀ r`
(closed-ball-complement form). -/
theorem variationalPerimeter_sdiff_ball_le_closedBall_compl_of_hasDerivAt
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μE : Measure (Space d)) [IsLocallyFiniteMeasure μE]
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    {x₀ : Space d} {r d' : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hderiv : HasDerivAt (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) d' r) :
    variationalPerimeter b (E \ ball x₀ r) Ω ≤
      μE (Ω \ closedBall x₀ r) + ENNReal.ofReal (ballGluingConstant * d') := by
  rw [← ballGluedSet_empty_left]
  have hsymm : symmDiff (∅ : Set (Space d)) E = E := by ext x; simp [symmDiff]
  have hd' : HasDerivAt (fun ρ ↦ volume.real ((symmDiff ∅ E) ∩ ball x₀ ρ)) d' r := by
    rwa [hsymm]
  have hbound := variationalPerimeter_ballGluedSet_le_closedBall_compl_of_hasDerivAt
    hd b MeasurableSet.empty hE hΩ (0 : Measure (Space d)) μE
    (fun U _ _ ↦ by simp) hμE hr hsub hd'
  simpa using hbound

/-- Pointwise derivative perimeter bound for the ball deletion competitor `E \ ball x₀ r`. -/
theorem variationalPerimeter_sdiff_ball_le_of_hasDerivAt
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μE : Measure (Space d)) [IsLocallyFiniteMeasure μE]
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    {x₀ : Space d} {r d' : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hderiv : HasDerivAt (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) d' r) :
    variationalPerimeter b (E \ ball x₀ r) Ω ≤
      μE (Ω \ ball x₀ r) + ENNReal.ofReal (ballGluingConstant * d') := by
  refine (variationalPerimeter_sdiff_ball_le_closedBall_compl_of_hasDerivAt
    hd b hE hΩ μE hμE hr hsub hderiv).trans ?_
  exact add_le_add (measure_mono fun _ hx ↦ ⟨hx.1, fun h ↦ hx.2 (ball_subset_closedBall h)⟩) le_rfl

/-- For Lebesgue-a.e. radius `r ∈ Ioo 0 R` (`ball x₀ R ⊆ Ω`), the ball deletion competitor
`E \ ball x₀ r` has perimeter in `Ω` bounded by `μE (Ω \ closedBall x₀ r) + C * deriv V_E r`. -/
theorem ae_radius_sdiff_ball_perimeter_le {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μE : Measure (Space d)) [IsLocallyFiniteMeasure μE]
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    (x₀ : Space d) {R : ℝ} (hsub : ball x₀ R ⊆ Ω) :
    ∀ᵐ r : ℝ ∂volume, r ∈ Ioo 0 R →
      μE (sphere x₀ r) = 0 ∧
      HasDerivAt (fun ρ ↦ volume.real (E ∩ ball x₀ ρ))
        (deriv (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) r) r ∧
      variationalPerimeter b (E \ ball x₀ r) Ω ≤
        μE (Ω \ closedBall x₀ r) +
          ENNReal.ofReal (ballGluingConstant *
            deriv (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) r) := by
  have hsymm : symmDiff (∅ : Set (Space d)) E = E := by ext x; simp [symmDiff]
  have hae := ae_radius_ballGluedSet_perimeter_le hd b MeasurableSet.empty hE hΩ
    (0 : Measure (Space d)) μE (fun U _ _ ↦ by simp) hμE x₀ hsub
  simp only [hsymm, ballGluedSet_empty_left, Measure.coe_zero, Pi.zero_apply, zero_add] at hae
  filter_upwards [hae] with r hr hmem
  obtain ⟨-, hsph, hdV, hperim⟩ := hr hmem
  exact ⟨hsph, hdV, hperim⟩

/-- Mean-value radius selection for ball deletion `E \ ball x₀ r` in `Ω`. -/
theorem exists_radius_sdiff_ball_perimeter_le {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μE : Measure (Space d)) [IsLocallyFiniteMeasure μE]
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    (x₀ : Space d) {a r_hi : ℝ} (ha : 0 < a) (har : a < r_hi) (hsub : ball x₀ r_hi ⊆ Ω) :
    ∃ r ∈ Ioo a r_hi,
      μE (sphere x₀ r) = 0 ∧
      HasDerivAt (fun ρ ↦ volume.real (E ∩ ball x₀ ρ))
        (deriv (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) r) r ∧
      deriv (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) r ≤
        volume.real (E ∩ (ball x₀ r_hi \ ball x₀ a)) / (r_hi - a) ∧
      variationalPerimeter b (E \ ball x₀ r) Ω ≤
        μE (Ω \ closedBall x₀ r) +
          ENNReal.ofReal (ballGluingConstant *
            deriv (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) r) := by
  have hsymm : symmDiff (∅ : Set (Space d)) E = E := by ext x; simp [symmDiff]
  obtain ⟨r, hr, -, hsph, hdV, hM, hperim⟩ :=
    exists_radius_ballGluedSet_perimeter_le hd b MeasurableSet.empty hE hΩ
      (0 : Measure (Space d)) μE (fun U _ _ ↦ by simp) hμE x₀ ha har hsub
  simp only [hsymm, ballGluedSet_empty_left, Measure.coe_zero, Pi.zero_apply, zero_add]
    at hdV hM hperim
  exact ⟨r, hr, hsph, hdV, hM, hperim⟩

/-- Cancelling the outer perimeter mass from a ball-deletion comparison bounds the interior
perimeter `μE (closedBall x₀ r)` (and `μE (ball x₀ r)`), provided `μE (Ω \ closedBall x₀ r) ≠ ⊤`. -/
theorem perimeter_closedBall_le_of_sdiff_ball_comparison
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μE : Measure (Space d)) [IsLocallyFiniteMeasure μE]
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    {x₀ : Space d} {r d' : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hfin : μE (Ω \ closedBall x₀ r) ≠ ⊤)
    (hmin : variationalPerimeter b E Ω ≤ variationalPerimeter b (E \ ball x₀ r) Ω)
    (hderiv : HasDerivAt (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) d' r) :
    μE (closedBall x₀ r) ≤ ENNReal.ofReal (ballGluingConstant * d') := by
  have hdel := variationalPerimeter_sdiff_ball_le_closedBall_compl_of_hasDerivAt
    hd b hE hΩ μE hμE hr hsub hderiv
  have htot : μE Ω ≤ μE (Ω \ closedBall x₀ r) + ENNReal.ofReal (ballGluingConstant * d') := by
    rw [hμE Ω hΩ Subset.rfl]
    exact hmin.trans hdel
  have hsplit : μE (closedBall x₀ r) + μE (Ω \ closedBall x₀ r) = μE Ω := by
    have hinter : Ω ∩ closedBall x₀ r = closedBall x₀ r := inter_eq_right.mpr hsub
    have hm := measure_inter_add_sdiff Ω (measurableSet_closedBall (x := x₀) (ε := r)) (μ := μE)
    rwa [hinter] at hm
  rw [← hsplit, add_comm (μE (Ω \ closedBall x₀ r))] at htot
  exact (ENNReal.add_le_add_iff_right hfin).mp htot

/-- Combining ball truncation with ball-deletion minimality bounds the global perimeter of
`E ∩ ball x₀ r` by `2 * ballGluingConstant * d'`. -/
theorem variationalPerimeter_inter_ball_univ_le_two_mul_of_sdiff_ball_comparison
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (μE : Measure (Space d)) [IsLocallyFiniteMeasure μE]
    (hμE : ∀ U, IsOpen U → U ⊆ Ω → μE U = variationalPerimeter b E U)
    {x₀ : Space d} {r d' : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hfin : μE (Ω \ closedBall x₀ r) ≠ ⊤)
    (hmin : variationalPerimeter b E Ω ≤ variationalPerimeter b (E \ ball x₀ r) Ω)
    (hderiv : HasDerivAt (fun ρ ↦ volume.real (E ∩ ball x₀ ρ)) d' r) :
    variationalPerimeter b (E ∩ ball x₀ r) univ ≤
      ENNReal.ofReal (2 * ballGluingConstant * d') := by
  have hd'_nonneg : 0 ≤ d' :=
    monotone_hasDerivAt_nonneg (monotone_volume_real_inter_ball E x₀) hderiv
  have htrunc := variationalPerimeter_inter_ball_univ_le_of_hasDerivAt
    hd b hE hΩ μE hμE hr hsub hderiv
  have hdel := perimeter_closedBall_le_of_sdiff_ball_comparison
    hd b hE hΩ μE hμE hr hsub hfin hmin hderiv
  have h0 : 0 ≤ ballGluingConstant * d' := mul_nonneg ballGluingConstant_pos.le hd'_nonneg
  calc
    variationalPerimeter b (E ∩ ball x₀ r) univ ≤
        ENNReal.ofReal (ballGluingConstant * d') + ENNReal.ofReal (ballGluingConstant * d') :=
      htrunc.trans (add_le_add hdel le_rfl)
    _ = ENNReal.ofReal (ballGluingConstant * d' + ballGluingConstant * d') :=
      (ENNReal.ofReal_add h0 h0).symm
    _ = ENNReal.ofReal (2 * ballGluingConstant * d') := by ring_nf

end SerrinEpigraph
