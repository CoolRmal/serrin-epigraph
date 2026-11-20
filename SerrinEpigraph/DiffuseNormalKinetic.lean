module

public import SerrinEpigraph.DiffusePlanarAlignment
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The normal kinetic bound along aligned planar blow-downs

This module proves the normal kinetic input `HasAlignedNormalKineticBound` of
`SerrinEpigraph.DiffusePlanarAlignment` (blueprint `harmonic-approximation.md` HA6:
`ν_j = ε (∂ₜ v_j)² dz ⇀ σ 𝓗ᵐ⌊{t = 0}`, here only the upper bound on vertical cylinders).

* **Vertical fundamental theorem of calculus** (`RigidityHypotheses.phasePrimitive_vertical_sub_le_integral`):
  for a normalized locally Lipschitz `v`, on almost every vertical line the jump of the phase
  primitive `Φ(v)` across `(-τ, τ)` is at most the energy on the segment, since
  `∂ₜ Φ(v) ≤ |∇Φ(v)| ≤ e_ε(v)` (Modica-free AM–GM, `competitorPrimitive_gradient_le_energy`)
  and `t ↦ Φ(v(y, t))` is absolutely continuous.
* **Slab lower bound** (`RigidityHypotheses.setIntegral_mul_phasePrimitive_jump_le`): by Fubini,
  `∫_B χ(y) (Φ(v(y, τ)) - Φ(v(y, -τ))) dy ≤ ∫_{B × (-τ, τ)} e_ε(v) χ(y)` for `χ ≥ 0` bounded.
* Along aligned sequences the jumps converge to `σ = Φ(1)` uniformly (HA8), so the slab energy
  is asymptotically at least `σ ∫_B χ`; with the sharp ball energy limit `σ ω_m` on `B₁`
  (`translated_energy_and_tilt_tendsto_of_halfspace_limit`) and the vanishing of the energy off
  the plane (`tendsto_energy_tail_of_aligned`), the complement of a cylinder in the unit ball
  carries at least its share, which bounds the cylinder energy, hence the normal kinetic mass
  (`ε (∂ₜ v)² ≤ e_ε(v)`), from above (`RigidityHypotheses.hasAlignedNormalKineticBound`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ## The vertical fundamental theorem of calculus for the phase primitive -/

theorem hasDerivAt_point_vertical (y : Space m) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ point y s) (verticalDirection m) t := by
  have h1 : HasDerivAt (fun s : ℝ ↦ ((y, s) : Space m × ℝ)) ((0 : Space m), (1 : ℝ)) t :=
    (hasDerivAt_const t y).prodMk (hasDerivAt_id t)
  have h2 := (pointContinuousLinearMap (m := m)).hasFDerivAt.comp_hasDerivAt t h1
  have h3 : pointContinuousLinearMap ((0 : Space m), (1 : ℝ)) = verticalDirection m :=
    point_zero_one_eq_vertical
  rw [h3] at h2
  exact h2

theorem contDiff_point_vertical (y : Space m) :
    ContDiff ℝ 1 (fun s : ℝ ↦ point y s) :=
  (pointContinuousLinearMap (m := m)).contDiff.comp (contDiff_const.prodMk contDiff_id)

/-- At a differentiability point of `v`, the vertical derivative of `t ↦ Φ(v(y, t))` is at most
the energy density. -/
theorem RigidityHypotheses.deriv_vertical_phasePrimitive_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hval : ∀ z, v z ∈ Icc (0 : ℝ) 1) {R : ℝ} (hR : 0 < R)
    {y : Space m} {t : ℝ} (hdiff : DifferentiableAt ℝ v (point y t)) :
    deriv (fun s ↦ phasePrimitive f (v (point y s))) t ≤
      rescaledPhaseEnergyDensity f R v (point y t) := by
  have hE0 := hr.rescaledPhaseEnergyDensity_nonneg h hR.le hval (point y t)
  by_cases hzero : v (point y t) = 0
  · have hmin : IsLocalMin (fun s ↦ phasePrimitive f (v (point y s))) t :=
      Eventually.of_forall fun s ↦ by
        simpa only [hzero, phasePrimitive_zero] using (h.phasePrimitive_mem_Icc (hval _)).1
    rw [hmin.deriv_eq_zero]
    exact hE0
  by_cases hone : v (point y t) = 1
  · have hmax : IsLocalMax (fun s ↦ phasePrimitive f (v (point y s))) t :=
      Eventually.of_forall fun s ↦ by
        simpa only [hone] using (h.phasePrimitive_mem_Icc (hval _)).2
    rw [hmax.deriv_eq_zero]
    exact hE0
  have hx : v (point y t) ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (hval _).1 (Ne.symm hzero), lt_of_le_of_ne (hval _).2 hone⟩
  have hFd : DifferentiableAt ℝ (fun z ↦ phasePrimitive f (v z)) (point y t) :=
    (h.phasePrimitive_hasDerivAt hx).differentiableAt.comp (point y t) hdiff
  have hG : HasDerivAt (fun s ↦ phasePrimitive f (v (point y s)))
      (fderiv ℝ (fun z ↦ phasePrimitive f (v z)) (point y t) (verticalDirection m)) t :=
    hFd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_point_vertical y t)
  rw [hG.deriv]
  calc fderiv ℝ (fun z ↦ phasePrimitive f (v z)) (point y t) (verticalDirection m)
      ≤ ‖fderiv ℝ (fun z ↦ phasePrimitive f (v z)) (point y t)‖ * ‖verticalDirection m‖ :=
        (le_abs_self _).trans (by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm _ _)
    _ = ‖gradient (fun z ↦ phasePrimitive f (v z)) (point y t)‖ := by
        rw [norm_verticalDirection, mul_one, gradient, LinearIsometryEquiv.norm_map]
    _ ≤ rescaledPhaseEnergyDensity f R v (point y t) :=
        hr.competitorPrimitive_gradient_le_energy h hval hR hdiff

/-- **Vertical FTC.** On a vertical line along which `v` is differentiable almost everywhere,
the jump of `Φ(v)` across `(-τ, τ)` is at most the energy of the segment. -/
theorem RigidityHypotheses.phasePrimitive_vertical_sub_le_integral
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hvL : LocallyLipschitz v) (hval : ∀ z, v z ∈ Icc (0 : ℝ) 1)
    {R : ℝ} (hR : 0 < R) {y : Space m} {τ : ℝ} (hτ : 0 < τ)
    (hae : ∀ᵐ t, DifferentiableAt ℝ v (point y t))
    (hint : IntegrableOn (fun t ↦ rescaledPhaseEnergyDensity f R v (point y t)) (Ioo (-τ) τ)) :
    phasePrimitive f (v (point y τ)) - phasePrimitive f (v (point y (-τ))) ≤
      ∫ t in Ioo (-τ) τ, rescaledPhaseEnergyDensity f R v (point y t) := by
  have hG : LocallyLipschitz (fun s ↦ phasePrimitive f (v (point y s))) :=
    (hr.phasePrimitive_comp_locallyLipschitz h hvL hval).comp
      (contDiff_point_vertical y).locallyLipschitz
  obtain ⟨K, hK⟩ := (hG.locallyLipschitzOn (s := uIcc (-τ) τ)).exists_lipschitzOnWith_of_compact
    isCompact_uIcc
  have hAC := LipschitzOnWith.absolutelyContinuousOnInterval hK
  have hFTC := hAC.integral_deriv_eq_sub
  rw [← hFTC, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  have hdint : IntegrableOn (deriv fun s ↦ phasePrimitive f (v (point y s))) (Ioo (-τ) τ) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      hAC.intervalIntegrable_deriv).mono_set Ioo_subset_Ioc_self
  refine setIntegral_mono_ae hdint hint ?_
  filter_upwards [hae] with t ht
  exact hr.deriv_vertical_phasePrimitive_le_energy h hval hR ht

/-! ## The slab lower bound -/

theorem norm_le_norm_horizontal_add_abs_last (z : Space (m + 1)) :
    ‖z‖ ≤ ‖horizontal z‖ + |z (Fin.last m)| := by
  have h3 := norm_sq_eq_horizontal_add_last_sq z
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [h3]
  nlinarith [abs_nonneg (z (Fin.last m)), sq_abs (z (Fin.last m)), norm_nonneg (horizontal z)]

/-- **Slab lower bound.** For a measurable bounded set `B` of horizontal points and a measurable
weight `χ`, nonnegative and bounded on `B`, the weighted energy of the slab `B × (-τ, τ)` is at
least the weighted jump of the phase primitive across it (Fubini and the vertical FTC). -/
theorem RigidityHypotheses.setIntegral_mul_phasePrimitive_jump_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hvL : LocallyLipschitz v) (hval : ∀ z, v z ∈ Icc (0 : ℝ) 1)
    {R : ℝ} (hR : 0 < R) {B : Set (Space m)} (hBm : MeasurableSet B)
    (hBb : Bornology.IsBounded B) {χ : Space m → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ y ∈ B, 0 ≤ χ y) {Cχ : ℝ} (hχC : ∀ y ∈ B, χ y ≤ Cχ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ y in B, χ y * (phasePrimitive f (v (point y τ)) - phasePrimitive f (v (point y (-τ))))) ≤
      ∫ z in horizontal ⁻¹' B ∩ (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-τ) τ,
        rescaledPhaseEnergyDensity f R v z * χ (horizontal z) := by
  set S : Set (Space (m + 1)) :=
    horizontal ⁻¹' B ∩ (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-τ) τ with hSdef
  have hcl : Continuous (fun z : Space (m + 1) ↦ (z (Fin.last m) : ℝ)) := continuous_last
  have hSm : MeasurableSet S :=
    (hBm.preimage continuous_horizontal.measurable).inter (measurableSet_Ioo.preimage hcl.measurable)
  obtain ⟨ρ, hρ⟩ := hBb.subset_closedBall (0 : Space m)
  have hSball : S ⊆ closedBall (0 : Space (m + 1)) (ρ + τ) := by
    intro z hz
    obtain ⟨hzB, hzt⟩ := hz
    have h1 : ‖horizontal z‖ ≤ ρ := by
      have := hρ hzB
      rwa [mem_closedBall, dist_zero_right] at this
    have h2 : |z (Fin.last m)| ≤ τ := abs_le.mpr ⟨hzt.1.le, hzt.2.le⟩
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_le_norm_horizontal_add_abs_last z]
  have hEint : IntegrableOn (rescaledPhaseEnergyDensity f R v) S :=
    (h.integrableOn_rescaledPhaseEnergy hvL hval R (isCompact_closedBall _ _)).mono_set hSball
  have hE0 : ∀ z, 0 ≤ rescaledPhaseEnergyDensity f R v z :=
    hr.rescaledPhaseEnergyDensity_nonneg h hR.le hval
  have hgS : IntegrableOn (fun z ↦ rescaledPhaseEnergyDensity f R v z * χ (horizontal z)) S := by
    refine (hEint.const_mul Cχ).mono' (hEint.aestronglyMeasurable.mul
      (hχm.comp continuous_horizontal.measurable).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hSm] with z hz
    have hzB : horizontal z ∈ B := hz.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hE0 z) (hχ0 _ hzB)), mul_comm]
    exact mul_le_mul_of_nonneg_right (hχC _ hzB) (hE0 z)
  set G : Space (m + 1) → ℝ :=
    S.indicator (fun z ↦ rescaledPhaseEnergyDensity f R v z * χ (horizontal z)) with hGdef
  have hGi : Integrable G := hgS.integrable_indicator hSm
  have hmp := measurePreserving_point m
  have hmap := integral_map hmp.measurable.aemeasurable
    (show AEStronglyMeasurable G
      (Measure.map (fun p : Space m × ℝ ↦ point p.1 p.2)
        ((volume : Measure (Space m)).prod volume))
      from by rw [hmp.map_eq]; exact hGi.aestronglyMeasurable)
  rw [hmp.map_eq] at hmap
  have hG'i : Integrable (fun p : Space m × ℝ ↦ G (point p.1 p.2))
      ((volume : Measure (Space m)).prod volume) := hmp.integrable_comp_of_integrable hGi
  have hslice : ∀ y : Space m, (∫ t, G (point y t)) =
      B.indicator (fun y ↦ χ y * ∫ t in Ioo (-τ) τ,
        rescaledPhaseEnergyDensity f R v (point y t)) y := by
    intro y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy, ← integral_const_mul, ← integral_indicator measurableSet_Ioo]
      refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
      dsimp only
      by_cases ht : t ∈ Ioo (-τ) τ
      · have hmem : point y t ∈ S := ⟨by simpa [horizontal_point] using hy,
          by simpa [last_point] using ht⟩
        simp only [hGdef, indicator_of_mem hmem, indicator_of_mem ht, horizontal_point]
        ring
      · have hmem : point y t ∉ S := fun hS ↦ ht (by simpa [last_point] using hS.2)
        simp only [hGdef, indicator_of_notMem hmem, indicator_of_notMem ht]
    · rw [indicator_of_notMem hy]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
      have hmem : point y t ∉ S := fun hS ↦ hy (by simpa [horizontal_point] using hS.1)
      simp only [hGdef, indicator_of_notMem hmem, Pi.zero_apply]
  -- the right-hand side as an iterated integral
  have hRHS : (∫ z in S, rescaledPhaseEnergyDensity f R v z * χ (horizontal z)) =
      ∫ y in B, χ y * ∫ t in Ioo (-τ) τ, rescaledPhaseEnergyDensity f R v (point y t) := by
    rw [← integral_indicator hSm, ← hGdef, hmap, integral_prod _ hG'i,
      ← integral_indicator hBm]
    exact integral_congr_ae (Eventually.of_forall hslice)
  rw [hRHS]
  -- integrability of both sides on `B`
  have hBfin : volume B ≠ ⊤ := ((measure_mono (hρ)).trans_lt measure_closedBall_lt_top).ne
  have hjump_c : Continuous (fun y : Space m ↦
      phasePrimitive f (v (point y τ)) - phasePrimitive f (v (point y (-τ)))) := by
    have hF := (hr.phasePrimitive_comp_locallyLipschitz h hvL hval).continuous
    exact (hF.comp (pointContinuousLinearMap.continuous.comp
        (continuous_id.prodMk continuous_const))).sub
      (hF.comp (pointContinuousLinearMap.continuous.comp (continuous_id.prodMk continuous_const)))
  have hσ := (h.phasePrimitive_mem_Icc (s := 1) ⟨zero_le_one, le_rfl⟩).1
  have hLi : IntegrableOn (fun y ↦ χ y *
      (phasePrimitive f (v (point y τ)) - phasePrimitive f (v (point y (-τ))))) B := by
    refine Measure.integrableOn_of_bounded (M := Cχ * phasePrimitive f 1) hBfin
      (hχm.aestronglyMeasurable.mul hjump_c.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hBm] with y hy
    have h1 := h.phasePrimitive_mem_Icc (hval (point y τ))
    have h2 := h.phasePrimitive_mem_Icc (hval (point y (-τ)))
    have h3 : |phasePrimitive f (v (point y τ)) - phasePrimitive f (v (point y (-τ)))| ≤
        phasePrimitive f 1 := by
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ0 y hy)]
    exact mul_le_mul (hχC y hy) h3 (abs_nonneg _) ((hχ0 y hy).trans (hχC y hy))
  have hRi : IntegrableOn (fun y ↦ χ y * ∫ t in Ioo (-τ) τ,
      rescaledPhaseEnergyDensity f R v (point y t)) B := by
    refine (hG'i.integral_prod_left.integrableOn (s := B)).congr_fun (fun y hy ↦ ?_) hBm
    change (∫ t, G (point y t)) = _
    rw [hslice y, indicator_of_mem hy]
  refine setIntegral_mono_ae_restrict hLi hRi ?_
  -- the pointwise comparison on almost every vertical line
  have hdiff := ae_vertical_of_ae_volume (ae_differentiableAt_of_locallyLipschitz hvL)
  have hsl := hG'i.prod_right_ae
  filter_upwards [ae_restrict_mem hBm, ae_restrict_of_ae hdiff, ae_restrict_of_ae hsl]
    with y hy hyd hys
  rcases (hχ0 y hy).eq_or_lt with hχy | hχy
  · rw [← hχy, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ hχy.le
    have hint : IntegrableOn (fun t ↦ rescaledPhaseEnergyDensity f R v (point y t))
        (Ioo (-τ) τ) := by
      have h1 : Integrable (fun t ↦ G (point y t)) := hys
      have h2 : (fun t ↦ G (point y t)) = (Ioo (-τ) τ).indicator
          (fun t ↦ rescaledPhaseEnergyDensity f R v (point y t) * χ y) := by
        funext t
        by_cases ht : t ∈ Ioo (-τ) τ
        · have hmem : point y t ∈ S := ⟨by simpa [horizontal_point] using hy,
            by simpa [last_point] using ht⟩
          rw [hGdef, indicator_of_mem hmem, indicator_of_mem ht, horizontal_point]
        · have hmem : point y t ∉ S := fun hS ↦ ht (by simpa [last_point] using hS.2)
          rw [hGdef, indicator_of_notMem hmem, indicator_of_notMem ht]
      rw [h2] at h1
      have h3 := ((integrable_indicator_iff measurableSet_Ioo).mp h1).mul_const (χ y)⁻¹
      refine IntegrableOn.congr_fun h3 (fun t _ ↦ ?_) measurableSet_Ioo
      have hne : χ y ≠ 0 := hχy.ne'
      field_simp
    exact hr.phasePrimitive_vertical_sub_le_integral h hvL hval hR hτ hyd hint

/-! ## The slab energy along aligned sequences -/

theorem RigidityHypotheses.integrableOn_rescaledEnergy_mul_bounded
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hvL : LocallyLipschitz v) (hval : ∀ z, v z ∈ Icc (0 : ℝ) 1)
    {R : ℝ} (hR : 0 ≤ R) {A : Set (Space (m + 1))} (hAb : Bornology.IsBounded A)
    {k : Space (m + 1) → ℝ} (hk : Measurable k) {K : ℝ} (hkK : ∀ z ∈ A, |k z| ≤ K)
    (hA : MeasurableSet A) :
    IntegrableOn (fun z ↦ rescaledPhaseEnergyDensity f R v z * k z) A := by
  obtain ⟨r, hr'⟩ := hAb.subset_closedBall (0 : Space (m + 1))
  have hE := (h.integrableOn_rescaledPhaseEnergy hvL hval R (isCompact_closedBall _ r)).mono_set hr'
  refine (hE.const_mul K).mono' (hE.aestronglyMeasurable.mul hk.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hA] with z hz
  have hE0 := hr.rescaledPhaseEnergyDensity_nonneg h hR hval z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hE0, mul_comm]
  exact mul_le_mul_of_nonneg_right (hkK z hz) hE0

theorem volume_real_ball_eq_pow_mul_closedBall {ρ : ℝ} (hρ : 0 < ρ) :
    volume.real (ball (0 : Space m) ρ) = ρ ^ m * volume.real (closedBall (0 : Space m) 1) := by
  rw [volume_real_ball_eq 0 hρ, measureReal_def, measureReal_def,
    Measure.addHaar_closedBall volume 0 zero_le_one, one_pow, ENNReal.ofReal_one, one_mul]
  ring

/-- Along an aligned sequence, the weighted energy of a slab `B × (-τ, τ)` is asymptotically at
least `σ ∫_B χ`: the jumps of `Φ(v_j)` across the slab tend to `Φ(1) - Φ(0) = σ` uniformly
(HA8). -/
theorem RigidityHypotheses.eventually_slab_energy_ge
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (x : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x j + R j • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0))
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    (hQ : Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e))
    {B : Set (Space m)} (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B)
    {χ : Space m → ℝ} (hχm : Measurable χ) (hχ0 : ∀ y ∈ B, 0 ≤ χ y) {Cχ : ℝ}
    (hχC : ∀ y ∈ B, χ y ≤ Cχ) {τ : ℝ} (hτ : 0 < τ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in atTop, phasePrimitive f 1 * (∫ y in B, χ y) - η ≤
      ∫ z in horizontal ⁻¹' B ∩ (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-τ) τ,
        rescaledPhaseEnergyDensity f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z *
          χ (horizontal z) := by
  have hV := hr.verticalPlanarLayers_of_rotated h hsharp x hR hRt he hlocal hQ
  obtain ⟨ρ, hρ⟩ := hBb.subset_closedBall (0 : Space m)
  set I : ℝ := ∫ y in B, χ y with hI
  have hBfin : volume B ≠ ⊤ := ((measure_mono hρ).trans_lt measure_closedBall_lt_top).ne
  have hI0 : 0 ≤ I := setIntegral_nonneg hBm hχ0
  have hLip := hr.phasePrimitive_lipschitzOn h
  set L : ℝ := Real.sqrt (2 * normalizedPotential f 0) with hL
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  set b : ℝ := η / (L * I + 1) with hb
  have hb0 : 0 < b := by positivity
  have hbη : L * b * I ≤ η := by
    rw [hb]
    have h1 : 0 < L * I + 1 := by positivity
    rw [show L * (η / (L * I + 1)) * I = η * (L * I / (L * I + 1)) by ring]
    have h2 : L * I / (L * I + 1) ≤ 1 := by
      rw [div_le_one h1]
      linarith
    nlinarith
  have hpt : ∀ y ∈ B, ‖point y τ‖ ≤ ρ + τ ∧ ‖point y (-τ)‖ ≤ ρ + τ := by
    intro y hy
    have h1 : ‖y‖ ≤ ρ := by
      have := hρ hy
      rwa [mem_closedBall, dist_zero_right] at this
    have h2 := norm_le_norm_horizontal_add_abs_last (point y τ)
    have h3 := norm_le_norm_horizontal_add_abs_last (point y (-τ))
    rw [horizontal_point, last_point, abs_of_pos hτ] at h2
    rw [horizontal_point, last_point, abs_neg, abs_of_pos hτ] at h3
    exact ⟨by linarith, by linarith⟩
  filter_upwards [hV.upper (ρ + τ) τ b hτ hb0, hV.lower (ρ + τ) τ hτ] with j hup hlow
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x j + R j • Q j z) with hvdef
  have hvL : LocallyLipschitz v :=
    locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz _ _ _
  have hval : ∀ z, v z ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hjump : ∀ y ∈ B, phasePrimitive f 1 - L * b ≤
      phasePrimitive f (v (point y τ)) - phasePrimitive f (v (point y (-τ))) := by
    intro y hy
    have h0 : v (point y (-τ)) = 0 := hlow (point y (-τ))
      (by rw [mem_closedBall, dist_zero_right]; exact (hpt y hy).2) (by rw [last_point])
    have h1 : 1 - b < v (point y τ) := hup (point y τ)
      (by rw [mem_closedBall, dist_zero_right]; exact (hpt y hy).1) (by rw [last_point])
    have h2 := hLip.dist_le_mul 1 ⟨zero_le_one, le_rfl⟩ (v (point y τ)) (hval _)
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hval _).2)] at h2
    have h3 : |phasePrimitive f 1 - phasePrimitive f (v (point y τ))| ≤ L * b := by
      refine h2.trans ?_
      change L * (1 - v (point y τ)) ≤ L * b
      exact mul_le_mul_of_nonneg_left (by linarith) hL0
    rw [h0, phasePrimitive_zero, sub_zero]
    linarith [(abs_le.mp h3).2]
  refine le_trans ?_ (hr.setIntegral_mul_phasePrimitive_jump_le h hvL hval (hR j) hBm hBb hχm
    hχ0 hχC hτ)
  have hconst : IntegrableOn (fun y ↦ χ y * (phasePrimitive f 1 - L * b)) B := by
    refine Measure.integrableOn_of_bounded (M := |Cχ| * |phasePrimitive f 1 - L * b|) hBfin
      (hχm.aestronglyMeasurable.mul aestronglyMeasurable_const) ?_
    filter_upwards [ae_restrict_mem hBm] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right ((abs_of_nonneg (hχ0 y hy)).le.trans
      ((hχC y hy).trans (le_abs_self _))) (abs_nonneg _)
  have hjc : Continuous (fun y : Space m ↦
      phasePrimitive f (v (point y τ)) - phasePrimitive f (v (point y (-τ)))) := by
    have hF := (hr.phasePrimitive_comp_locallyLipschitz h hvL hval).continuous
    exact (hF.comp (pointContinuousLinearMap.continuous.comp
        (continuous_id.prodMk continuous_const))).sub
      (hF.comp (pointContinuousLinearMap.continuous.comp (continuous_id.prodMk continuous_const)))
  have hjumpi : IntegrableOn (fun y ↦ χ y *
      (phasePrimitive f (v (point y τ)) - phasePrimitive f (v (point y (-τ))))) B := by
    refine Measure.integrableOn_of_bounded (M := |Cχ| * phasePrimitive f 1) hBfin
      (hχm.aestronglyMeasurable.mul hjc.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hBm] with y hy
    have h1 := h.phasePrimitive_mem_Icc (hval (point y τ))
    have h2 := h.phasePrimitive_mem_Icc (hval (point y (-τ)))
    have h3 : |phasePrimitive f (v (point y τ)) - phasePrimitive f (v (point y (-τ)))| ≤
        phasePrimitive f 1 := by
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((abs_of_nonneg (hχ0 y hy)).le.trans ((hχC y hy).trans (le_abs_self _)))
      h3 (abs_nonneg _) (abs_nonneg _)
  calc phasePrimitive f 1 * I - η ≤ (phasePrimitive f 1 - L * b) * I := by nlinarith
    _ = ∫ y in B, χ y * (phasePrimitive f 1 - L * b) := by
        rw [hI, integral_mul_const, mul_comm]
    _ ≤ ∫ y in B, χ y *
        (phasePrimitive f (v (point y τ)) - phasePrimitive f (v (point y (-τ)))) :=
        setIntegral_mono_on hconst hjumpi hBm fun y hy ↦
          mul_le_mul_of_nonneg_left (hjump y hy) (hχ0 y hy)

/-! ## The normal kinetic bound -/

/-- Energies on centered balls do not see the rotation of the rescaling. -/
theorem setIntegral_closedBall_rescaled_isometry (f : ℝ → ℝ) (U : Space (m + 1) → ℝ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (r : ℝ) :
    (∫ z in closedBall (0 : Space (m + 1)) r,
      rescaledPhaseEnergyDensity f R (fun y ↦ U (c + R • Q y)) z) =
      ∫ z in closedBall (0 : Space (m + 1)) r,
        rescaledPhaseEnergyDensity f R (fun y ↦ U (c + R • y)) z := by
  set F : Space (m + 1) → ℝ := fun w ↦ R * phaseEnergyDensity f 0 U (c + R • w) with hF
  have h1 : ∀ z, rescaledPhaseEnergyDensity f R (fun y ↦ U (c + R • Q y)) z = F (Q z) :=
    fun z ↦ rescaledPhaseEnergyDensity_translate_dilation_isometry f U c hR Q z
  have h2 : ∀ z, rescaledPhaseEnergyDensity f R (fun y ↦ U (c + R • y)) z = F z :=
    fun z ↦ rescaledPhaseEnergyDensity_translate_dilation_isometry f U c hR
      (LinearIsometryEquiv.refl ℝ _) z
  have h3 := Q.measurePreserving.setIntegral_preimage_emb Q.toHomeomorph.measurableEmbedding F
    (closedBall (0 : Space (m + 1)) r)
  rw [Q.preimage_closedBall, map_zero] at h3
  rw [setIntegral_congr_fun measurableSet_closedBall (fun z _ ↦ h1 z), h3,
    setIntegral_congr_fun measurableSet_closedBall (fun z _ ↦ h2 z)]

/-- **The normal kinetic bound (ν).** Along aligned planar blow-down sequences, the normal
kinetic mass of the rotated rescalings in `Q_s`, weighted by `w(y) ≥ 0`, is asymptotically at
most `σ ∫_{B_s} w`, `σ = Φ(1)`. -/
theorem RigidityHypotheses.hasAlignedNormalKineticBound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    HasAlignedNormalKineticBound g u (phasePrimitive f 1) := by
  intro x R Q e hx hR hRt he hlocal hQ s hs w hw hw0 η hη
  have hσ : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  set σ : ℝ := phasePrimitive f 1 with hσdef
  set ω : ℝ := volume.real (closedBall (0 : Space m) 1) with hωdef
  have hω : 0 ≤ ω := measureReal_nonneg
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Space m) 1).exists_bound_of_continuousOn
    hw.continuousOn
  set W : ℝ := max C 0 with hWdef
  have hW0 : 0 ≤ W := le_max_right _ _
  have hwW : ∀ y ∈ closedBall (0 : Space m) 1, w y ≤ W := fun y hy ↦
    (le_abs_self _).trans ((Real.norm_eq_abs (w y) ▸ hC y hy).trans (le_max_left _ _))
  -- the radius `ρ' = 1 - θ` and the slab height `h₀`
  set θ : ℝ := min (1 / 4) (η / (4 * (σ * W * ω * m + 1))) with hθ
  have hA0 : 0 ≤ σ * W * ω * m := by positivity
  have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ14 : θ ≤ 1 / 4 := min_le_left _ _
  set ρ' : ℝ := 1 - θ with hρ'
  have hρ'pos : 0 < ρ' := by linarith
  have hbern : σ * W * ω * (1 - ρ' ^ m) ≤ η / 4 := by
    have h1 := one_add_le_pow_of_two_add_nonneg (a := -θ) (by linarith) m
    have h2 : 1 - ρ' ^ m ≤ m * θ := by
      have h3 : 1 + -θ = ρ' := by rw [hρ']; ring
      rw [h3] at h1
      linarith
    have h3 : θ ≤ η / (4 * (σ * W * ω * m + 1)) := min_le_right _ _
    have hX : σ * W * ω * m * (η / (4 * (σ * W * ω * m + 1))) ≤ η / 4 := by
      have h4 : 0 < σ * W * ω * m + 1 := by positivity
      rw [show σ * W * ω * m * (η / (4 * (σ * W * ω * m + 1))) =
        η / 4 * (σ * W * ω * m / (σ * W * ω * m + 1)) by field_simp]
      have h5 : σ * W * ω * m / (σ * W * ω * m + 1) ≤ 1 := by
        rw [div_le_one h4]
        linarith
      nlinarith
    calc σ * W * ω * (1 - ρ' ^ m) ≤ σ * W * ω * (m * θ) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = σ * W * ω * m * θ := by ring
      _ ≤ σ * W * ω * m * (η / (4 * (σ * W * ω * m + 1))) :=
          mul_le_mul_of_nonneg_left h3 hA0
      _ ≤ η / 4 := hX
  set h₀ : ℝ := min s θ with hh₀
  have hh₀pos : 0 < h₀ := lt_min hs.1 hθ0
  have hh₀s : h₀ ≤ s := min_le_left _ _
  have hh₀θ : h₀ ≤ θ := min_le_right _ _
  have hsρ : s < ρ' := by linarith [hs.2]
  -- the sets
  have hcl : Continuous (fun z : Space (m + 1) ↦ (z (Fin.last m) : ℝ)) := continuous_last
  set Qs : Set (Space (m + 1)) := tiltCylinder (verticalDirection m) s with hQs
  set T : Set (Space (m + 1)) := {z | |z (Fin.last m)| < h₀} with hT
  have hTm : MeasurableSet T := (isOpen_lt (continuous_abs.comp hcl) continuous_const).measurableSet
  have hQsm : MeasurableSet Qs := (isOpen_tiltCylinder _ _).measurableSet
  set Bρ : Set (Space m) := ball (0 : Space m) ρ' with hBρ
  set S' : Set (Space (m + 1)) :=
    horizontal ⁻¹' Bρ ∩ (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-h₀) h₀ with hS'
  have hS'm : MeasurableSet S' := (measurableSet_ball.preimage continuous_horizontal.measurable).inter
    (measurableSet_Ioo.preimage hcl.measurable)
  set wt : Space m → ℝ := (ball (0 : Space m) s).indicator w with hwt
  have hwtm : Measurable wt := hw.measurable.indicator measurableSet_ball
  set χ : Space m → ℝ := fun y ↦ W - wt y with hχ
  have hQs1 : Qs ⊆ closedBall (0 : Space (m + 1)) 1 := (ha6_tiltCylinder_subset_closedBall s).trans
    (closedBall_subset_closedBall (by linarith [hs.2]))
  have hS'1 : S' ⊆ closedBall (0 : Space (m + 1)) 1 := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have h1 : ‖horizontal z‖ < ρ' := by
      have hz1' : horizontal z ∈ ball (0 : Space m) ρ' := hz1
      rwa [mem_ball, dist_zero_right] at hz1'
    have h2 : |z (Fin.last m)| < h₀ := abs_lt.mpr hz2
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_le_norm_horizontal_add_abs_last z]
  have hA1 : Qs ∩ T ⊆ S' := by
    intro z hz
    obtain ⟨hzQ, hzT⟩ := hz
    have h1 := (mem_tiltCylinder_vertical_iff.mp hzQ).1
    refine ⟨?_, abs_lt.mp hzT⟩
    show horizontal z ∈ ball (0 : Space m) ρ'
    rw [mem_ball, dist_zero_right]
    linarith
  have hA2 : Qs \ T ⊆ tiltCylinder (verticalDirection m) 2 ∩
      {z : Space (m + 1) | h₀ ≤ |z (Fin.last m)|} := by
    intro z hz
    obtain ⟨hzQ, hzT⟩ := hz
    refine ⟨tiltCylinder_mono _ (by linarith [hs.2]) hzQ, ?_⟩
    simpa [hT] using hzT
  have hwtW : ∀ y ∈ Bρ, 0 ≤ wt y ∧ wt y ≤ W := by
    intro y hy
    have hy1 : y ∈ closedBall (0 : Space m) 1 := by
      have : ‖y‖ < ρ' := by
        have hy' : y ∈ ball (0 : Space m) ρ' := hy
        rwa [mem_ball, dist_zero_right] at hy'
      rw [mem_closedBall, dist_zero_right]
      linarith
    by_cases hys : y ∈ ball (0 : Space m) s
    · rw [hwt, indicator_of_mem hys]
      exact ⟨hw0 y, hwW y hy1⟩
    · rw [hwt, indicator_of_notMem hys]
      exact ⟨le_rfl, hW0⟩
  -- the three eventual estimates
  have hE1 : ∀ᶠ j in atTop, W * (∫ z in closedBall (0 : Space (m + 1)) 1,
      rescaledPhaseEnergyDensity f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z) ≤
        W * (σ * ω) + η / 4 := by
    obtain ⟨-, hE, -⟩ := hr.translated_energy_and_tilt_tendsto_of_halfspace_limit h hsharp x hR
      he hlocal (r := 1) one_pos
    rw [one_pow, one_mul] at hE
    have hE' := hE.const_mul W
    have hlt : W * (σ * ω) < W * (σ * ω) + η / 4 := by linarith
    filter_upwards [hE'.eventually_lt_const hlt] with j hj
    rw [setIntegral_closedBall_rescaled_isometry f (zeroExtension g u) (x j) (hR j) (Q j) 1]
    exact hj.le
  have hE2 := hr.eventually_slab_energy_ge h hsharp x hR hRt he hlocal hQ
    (B := Bρ) measurableSet_ball isBounded_ball (χ := χ) (measurable_const.sub hwtm)
    (fun y hy ↦ by have := hwtW y hy; simp only [hχ]; linarith) (Cχ := W)
    (fun y hy ↦ by have := hwtW y hy; simp only [hχ]; linarith) hh₀pos
    (η := η / 4) (by positivity)
  have hE3 : ∀ᶠ j in atTop, W * (∫ z in tiltCylinder (verticalDirection m) 2 ∩
      {z | h₀ ≤ |z (Fin.last m)|},
        rescaledPhaseEnergyDensity f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z) ≤
          η / 4 := by
    have ht := hr.tendsto_energy_tail_of_aligned h hsharp x hR hRt (δ := fun _ ↦ 1)
      (fun _ ↦ one_pos) (by simpa using hRt) he hlocal hQ (r := 2) two_pos hh₀pos
    simp only [inv_one, one_pow, one_mul] at ht
    have ht' := ht.const_mul W
    rw [mul_zero] at ht'
    filter_upwards [ht'.eventually_lt_const (by positivity : (0 : ℝ) < η / 4)] with j hj
    exact hj.le
  filter_upwards [hE1, hE2, hE3] with j hj1 hj2 hj3
  -- the estimate at index `j`
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x j + R j • Q j z) with hvdef
  have hvL : LocallyLipschitz v :=
    locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz _ _ _
  have hval : ∀ z, v z ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hRj := hR j
  have hE0 : ∀ z, 0 ≤ rescaledPhaseEnergyDensity f (R j) v z :=
    hr.rescaledPhaseEnergyDensity_nonneg h hRj.le hval
  have hEN : ∀ z, verticalDerivative v z ^ 2 / R j ≤ rescaledPhaseEnergyDensity f (R j) v z := by
    intro z
    have := hr.rescaled_isometry_energy_sub_vertical_sq_nonneg h (x j) hRj (Q j) z
    rw [div_eq_inv_mul]
    linarith
  have hwQs : ∀ z ∈ Qs, 0 ≤ w (horizontal z) ∧ w (horizontal z) ≤ W := by
    intro z hz
    refine ⟨hw0 _, hwW _ ?_⟩
    have h1 := (mem_tiltCylinder_vertical_iff.mp hz).1
    rw [mem_closedBall, dist_zero_right]
    linarith [hs.2]
  -- integrability
  have iN : IntegrableOn (fun z ↦ verticalDerivative v z ^ 2 / R j * w (horizontal z)) Qs := by
    refine integrableOn_of_abs_le_mul_gradient_sq hvL ?_ hQsm
      (isBounded_tiltCylinder (norm_verticalDirection m) s) (C := (R j)⁻¹ * W) fun z hz ↦ ?_
    · exact (((measurable_verticalDerivative v).pow_const 2).div_const _).mul
        (hw.measurable.comp continuous_horizontal.measurable)
    · obtain ⟨h0, h1⟩ := hwQs z hz
      rw [abs_of_nonneg (by positivity)]
      have h2 := verticalDerivative_sq_le_gradient v z
      calc verticalDerivative v z ^ 2 / R j * w (horizontal z)
          = (R j)⁻¹ * (verticalDerivative v z ^ 2 * w (horizontal z)) := by ring
        _ ≤ (R j)⁻¹ * (‖gradient v z‖ ^ 2 * W) := by gcongr
        _ = (R j)⁻¹ * W * ‖gradient v z‖ ^ 2 := by ring
  have iEw : IntegrableOn (fun z ↦ rescaledPhaseEnergyDensity f (R j) v z * w (horizontal z)) Qs :=
    hr.integrableOn_rescaledEnergy_mul_bounded h hvL hval hRj.le
      (isBounded_tiltCylinder (norm_verticalDirection m) s)
      (hw.measurable.comp continuous_horizontal.measurable) (K := W)
      (fun z hz ↦ by rw [abs_of_nonneg (hwQs z hz).1]; exact (hwQs z hz).2) hQsm
  have hS'B : ∀ z ∈ S', horizontal z ∈ Bρ := fun z hz ↦ hz.1
  have iEwt : IntegrableOn (fun z ↦ rescaledPhaseEnergyDensity f (R j) v z * wt (horizontal z))
      S' :=
    hr.integrableOn_rescaledEnergy_mul_bounded h hvL hval hRj.le
      (isBounded_closedBall.subset hS'1) (hwtm.comp continuous_horizontal.measurable) (K := W)
      (fun z hz ↦ by
        obtain ⟨h0, h1⟩ := hwtW _ (hS'B z hz)
        rw [abs_of_nonneg h0]
        exact h1) hS'm
  have iEchi : IntegrableOn (fun z ↦ rescaledPhaseEnergyDensity f (R j) v z * χ (horizontal z))
      S' :=
    hr.integrableOn_rescaledEnergy_mul_bounded h hvL hval hRj.le
      (isBounded_closedBall.subset hS'1)
      ((measurable_const.sub hwtm).comp continuous_horizontal.measurable) (K := W)
      (fun z hz ↦ by
        obtain ⟨h0, h1⟩ := hwtW _ (hS'B z hz)
        simp only [hχ]
        rw [abs_of_nonneg (by linarith)]
        linarith) hS'm
  have iE1 : IntegrableOn (rescaledPhaseEnergyDensity f (R j) v) (closedBall 0 1) :=
    h.integrableOn_rescaledPhaseEnergy hvL hval (R j) (isCompact_closedBall _ _)
  have iET : IntegrableOn (rescaledPhaseEnergyDensity f (R j) v)
      (tiltCylinder (verticalDirection m) 2 ∩ {z : Space (m + 1) | h₀ ≤ |z (Fin.last m)|}) :=
    (h.integrableOn_rescaledPhaseEnergy hvL hval (R j) (isCompact_closedBall _ 4)).mono_set
      (inter_subset_left.trans ((ha6_tiltCylinder_subset_closedBall 2).trans
        (closedBall_subset_closedBall (by norm_num))))
  -- step 1: the normal kinetic mass is at most the weighted energy
  have st1 : (∫ z in Qs, verticalDerivative v z ^ 2 / R j * w (horizontal z)) ≤
      ∫ z in Qs, rescaledPhaseEnergyDensity f (R j) v z * w (horizontal z) :=
    setIntegral_mono_on iN iEw hQsm fun z hz ↦
      mul_le_mul_of_nonneg_right (hEN z) (hwQs z hz).1
  -- step 2: split off the part away from the plane
  have st2 : (∫ z in Qs \ T, rescaledPhaseEnergyDensity f (R j) v z * w (horizontal z)) ≤
      η / 4 := by
    have h1 : (∫ z in Qs \ T, rescaledPhaseEnergyDensity f (R j) v z * w (horizontal z)) ≤
        ∫ z in Qs \ T, W * rescaledPhaseEnergyDensity f (R j) v z :=
      setIntegral_mono_on (iEw.mono_set sdiff_subset)
        ((iET.mono_set hA2).const_mul W) (hQsm.diff hTm) fun z hz ↦ by
          rw [mul_comm W]
          exact mul_le_mul_of_nonneg_left (hwQs z hz.1).2 (hE0 z)
    have h2 : (∫ z in Qs \ T, W * rescaledPhaseEnergyDensity f (R j) v z) ≤
        W * ∫ z in tiltCylinder (verticalDirection m) 2 ∩
          {z : Space (m + 1) | h₀ ≤ |z (Fin.last m)|}, rescaledPhaseEnergyDensity f (R j) v z := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (setIntegral_mono_set iET
        (Eventually.of_forall fun z ↦ hE0 z) (Eventually.of_forall hA2)) hW0
    exact h1.trans (h2.trans hj3)
  -- step 3: the part near the plane, through the slab
  have st3 : (∫ z in Qs ∩ T, rescaledPhaseEnergyDensity f (R j) v z * w (horizontal z)) ≤
      ∫ z in S', rescaledPhaseEnergyDensity f (R j) v z * wt (horizontal z) := by
    have h1 : (∫ z in Qs ∩ T, rescaledPhaseEnergyDensity f (R j) v z * w (horizontal z)) =
        ∫ z in Qs ∩ T, rescaledPhaseEnergyDensity f (R j) v z * wt (horizontal z) := by
      refine setIntegral_congr_fun (hQsm.inter hTm) fun z hz ↦ ?_
      have hz1 : horizontal z ∈ ball (0 : Space m) s := by
        have := (mem_tiltCylinder_vertical_iff.mp hz.1).1
        rwa [mem_ball, dist_zero_right]
      simp only [hwt, indicator_of_mem hz1]
    rw [h1]
    refine setIntegral_mono_set iEwt (Eventually.of_forall fun z ↦ ?_)
      (Eventually.of_forall hA1)
    obtain ⟨h0, -⟩ := (by
      by_cases hzB : horizontal z ∈ Bρ
      · exact hwtW _ hzB
      · have : wt (horizontal z) = 0 := by
          rw [hwt, indicator_of_notMem]
          intro hzs
          exact hzB (ball_subset_ball hsρ.le hzs)
        rw [this]
        exact ⟨le_rfl, hW0⟩ : 0 ≤ wt (horizontal z) ∧ wt (horizontal z) ≤ W)
    exact mul_nonneg (hE0 z) h0
  -- step 4: the slab identity `E wt = W E - E χ`
  have st4 : (∫ z in S', rescaledPhaseEnergyDensity f (R j) v z * wt (horizontal z)) =
      W * (∫ z in S', rescaledPhaseEnergyDensity f (R j) v z) -
        ∫ z in S', rescaledPhaseEnergyDensity f (R j) v z * χ (horizontal z) := by
    rw [← integral_const_mul, ← integral_sub ((iE1.mono_set hS'1).const_mul W) iEchi]
    refine setIntegral_congr_fun hS'm fun z _ ↦ ?_
    simp only [hχ]
    ring
  -- step 5: the integral of `χ`
  have st5 : (∫ y in Bρ, χ y) = W * (ρ' ^ m * ω) - ∫ y in ball (0 : Space m) s, w y := by
    have iw : IntegrableOn wt Bρ := by
      refine Measure.integrableOn_of_bounded (M := W) measure_ball_lt_top.ne
        hwtm.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      obtain ⟨h0, h1⟩ := hwtW y hy
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
    have ic : IntegrableOn (fun _ : Space m ↦ W) Bρ :=
      integrableOn_const (C := W) measure_ball_lt_top.ne
    simp only [hχ]
    rw [integral_sub ic iw, setIntegral_const,
      smul_eq_mul, hBρ, volume_real_ball_eq_pow_mul_closedBall hρ'pos, hwt,
      setIntegral_indicator measurableSet_ball,
      inter_eq_right.mpr (ball_subset_ball hsρ.le)]
    ring
  -- step 6: combine
  have hsplit := integral_inter_add_sdiff hTm iEw
  have hS'E : W * (∫ z in S', rescaledPhaseEnergyDensity f (R j) v z) ≤
      W * ∫ z in closedBall (0 : Space (m + 1)) 1, rescaledPhaseEnergyDensity f (R j) v z :=
    mul_le_mul_of_nonneg_left (setIntegral_mono_set iE1 (Eventually.of_forall fun z ↦ hE0 z)
      (Eventually.of_forall hS'1)) hW0
  have hj1' : W * (∫ z in closedBall (0 : Space (m + 1)) 1,
      rescaledPhaseEnergyDensity f (R j) v z) ≤ W * (σ * ω) + η / 4 := hj1
  have hj2' : σ * (∫ y in Bρ, χ y) - η / 4 ≤
      ∫ z in S', rescaledPhaseEnergyDensity f (R j) v z * χ (horizontal z) := hj2
  rw [st5] at hj2'
  have hkey : σ * (W * (ρ' ^ m * ω) - ∫ y in ball (0 : Space m) s, w y) =
      σ * W * ω * ρ' ^ m - σ * ∫ y in ball (0 : Space m) s, w y := by ring
  rw [hkey] at hj2'
  have hbern' : σ * W * ω - σ * W * ω * ρ' ^ m ≤ η / 4 := by
    have := hbern
    linarith [show σ * W * ω * (1 - ρ' ^ m) = σ * W * ω - σ * W * ω * ρ' ^ m by ring]
  calc (∫ z in Qs, verticalDerivative v z ^ 2 / R j * w (horizontal z))
      ≤ ∫ z in Qs, rescaledPhaseEnergyDensity f (R j) v z * w (horizontal z) := st1
    _ = (∫ z in Qs ∩ T, rescaledPhaseEnergyDensity f (R j) v z * w (horizontal z)) +
        ∫ z in Qs \ T, rescaledPhaseEnergyDensity f (R j) v z * w (horizontal z) := hsplit.symm
    _ ≤ σ * (∫ y in ball (0 : Space m) s, w y) + η := by
        rw [st4] at st3
        nlinarith [st2, st3, hS'E, hj1', hj2', hbern']

/-! ## HA0 from the HA4/HA6.1 inputs -/

/-- **HA0 (`HasCylinderTiltDecay`) from the HA4/HA6.1 inputs alone.** Under the hypotheses of
`RigidityHypotheses.hasCylinderTiltDecay_of_sharp_energy`, the HA0 cylinder tilt decay follows
from `HasAlignedHarmonicLayerData g u (phasePrimitive f 1) M` for some `M ≥ 0`: the normal
kinetic bound (ν) is `RigidityHypotheses.hasAlignedNormalKineticBound`, the energy tails, the
alignment of the HA11 sequences, HA6, HA7 and the HA11 contradiction argument are proved in
`DiffusePlanarAlignment`, `DiffuseHarmonicApproximation` and `DiffuseTiltDecay`. -/
theorem RigidityHypotheses.hasCylinderTiltDecay_of_harmonicLayerData
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {M : ℝ} (hM : 0 ≤ M) (hal : HasAlignedHarmonicLayerData g u (phasePrimitive f 1) M) :
    HasCylinderTiltDecay g u :=
  hr.hasCylinderTiltDecay_of_alignedLayerData h hsharp hM hal
    (hr.hasAlignedNormalKineticBound h hsharp)

end SerrinEpigraph
