module

public import SerrinEpigraph.PhysicalTranslationStress
public import SerrinEpigraph.PlaneTiltPoissonScaling
public import SerrinEpigraph.PlaneTiltTranslatedClearing
public import SerrinEpigraph.StableWellTranslation
public import SerrinEpigraph.GluingTotalEnergy
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rescaled stress identities, Caccioppoli bounds, horizontal flux and exponential tails

This file establishes the diffuse-interface estimates FE2, FE3 and FE4 from
`docs/rigidity-proof/flatness-estimates.md`:
1. Spatial stress stationarity and the Modica bound for rotated, translated and dilated
   zero extensions `x ↦ zeroExtension g u (c + R • Q x)`.
2. Product-coordinate vertical stress identities, the localized height stress identity and
   the one-phase Caccioppoli inequality with explicit cutoff errors (FE2).
3. The horizontal normal-flux identity and boundary cutoff error bound (FE4).
4. Second-order potential coercivity bounds near `1`, the explicit `cosh` cube barrier,
   quantitative exponential phase and energy tails (FE3), and power-exponential decay limits.
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Laplacian ContDiff Pointwise

namespace SerrinEpigraph

/-! ### Rotated and translated rescaling calculus -/

/-- Totalized gradient chain rule under translation, dilation and linear Euclidean isometry. -/
theorem gradient_comp_translate_dilation_isometry {d : ℕ} (U : Space d → ℝ)
    (c : Space d) (R : ℝ) (Q : Space d ≃ₗᵢ[ℝ] Space d) (x : Space d) :
    gradient (fun y ↦ U (c + R • Q y)) x = R • Q.symm (gradient U (c + R • Q x)) := by
  let w : Space d → ℝ := fun z ↦ U (c + R • z)
  change gradient (fun y ↦ w (Q y)) x = _
  rw [gradient_comp_linearIsometryEquiv w Q x, gradient_comp_translate_dilation, map_smul]

/-- Local Lipschitz regularity is preserved by translation, dilation and linear isometry. -/
theorem locallyLipschitz_comp_translate_dilation_isometry {d : ℕ} {U : Space d → ℝ}
    (hU : LocallyLipschitz U) (c : Space d) (R : ℝ) (Q : Space d ≃ₗᵢ[ℝ] Space d) :
    LocallyLipschitz (fun y ↦ U (c + R • Q y)) :=
  (locallyLipschitz_comp_translate_dilation hU c R).comp Q.lipschitzWith.locallyLipschitz

/-- Rescaled energy density under translation, dilation and linear Euclidean isometry. -/
theorem rescaledPhaseEnergyDensity_translate_dilation_isometry {d : ℕ} (f : ℝ → ℝ)
    (U : Space d → ℝ) (c : Space d) {R : ℝ} (hR : 0 < R)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (x : Space d) :
    rescaledPhaseEnergyDensity f R (fun y ↦ U (c + R • Q y)) x =
      R * phaseEnergyDensity f 0 U (c + R • Q x) := by
  by_cases hx : 0 < U (c + R • Q x)
  · simp only [rescaledPhaseEnergyDensity, phaseEnergyDensity, indicator_apply, mem_ofPred_eq,
      hx, ite_true, gradient_comp_translate_dilation_isometry, norm_smul, Q.symm.norm_map,
      Real.norm_of_nonneg hR.le, add_zero]
    field_simp
  · simp [rescaledPhaseEnergyDensity, phaseEnergyDensity, hx]

/-- Classical Laplacian invariance under a linear Euclidean isometry. -/
theorem laplacian_comp_linearIsometryEquiv_of_contDiffAt {d : ℕ} {U : Space d → ℝ}
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (x : Space d) (hU : ContDiffAt ℝ 2 U (Q x)) :
    (Δ (fun y ↦ U (Q y))) x = (Δ U) (Q x) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hw : ContDiffAt ℝ 2 (fun y ↦ U (Q y)) x := hU.comp x Q.contDiff.contDiffAt
  have hdU := (hU.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hdw := (hw.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  rw [laplacian_eq_sum_fderiv b hdw, laplacian_eq_sum_fderiv (b.map Q) hdU]
  apply Finset.sum_congr rfl
  intro i _
  have h1 (y : Space d) : fderiv ℝ (fun z ↦ U (Q z)) y (b i) = fderiv ℝ U (Q y) (Q (b i)) := by
    have he := Q.toContinuousLinearEquiv.comp_right_fderiv (f := U) (x := y)
    exact congrArg (fun L : Space d →L[ℝ] ℝ ↦ L (b i)) he
  simp_rw [h1, OrthonormalBasis.map_apply]
  have he2 := Q.toContinuousLinearEquiv.comp_right_fderiv
    (f := fun z ↦ fderiv ℝ U z (Q (b i))) (x := x)
  exact congrArg (fun L : Space d →L[ℝ] ℝ ↦ L (b i)) he2

/-- Classical Laplacian scaling under translation, dilation and linear Euclidean isometry. -/
theorem laplacian_comp_translate_dilation_isometry_of_contDiffAt {d : ℕ} {U : Space d → ℝ}
    (c : Space d) (R : ℝ) (Q : Space d ≃ₗᵢ[ℝ] Space d) (x : Space d)
    (hU : ContDiffAt ℝ 2 U (c + R • Q x)) :
    (Δ (fun y ↦ U (c + R • Q y))) x = R ^ 2 * (Δ U) (c + R • Q x) := by
  have ht : ContDiffAt ℝ 2 (fun z ↦ U (c + R • z)) (Q x) :=
    hU.comp (Q x) ((contDiff_const.add (contDiff_id.const_smul R)).contDiffAt)
  let w : Space d → ℝ := fun z ↦ U (c + R • z)
  change (Δ (fun y ↦ w (Q y))) x = _
  rw [laplacian_comp_linearIsometryEquiv_of_contDiffAt Q x ht,
    laplacian_comp_translate_dilation_of_contDiffAt c R (Q x) hU]

/-! ### Horizontal and vertical gradient decomposition -/

theorem inner_verticalDirection_right {m : ℕ} (p : Space (m + 1)) :
    inner ℝ p (verticalDirection m) = p (Fin.last m) := by
  simp [verticalDirection, EuclideanSpace.inner_single_right]

theorem inner_gradient_verticalDirection {m : ℕ} (v : Space (m + 1) → ℝ) (x : Space (m + 1)) :
    inner ℝ (gradient v x) (verticalDirection m) = verticalDerivative v x := by
  rw [inner_gradient_left]
  rfl

theorem gradient_last_eq_verticalDerivative {m : ℕ} (v : Space (m + 1) → ℝ) (x : Space (m + 1)) :
    gradient v x (Fin.last m) = verticalDerivative v x := by
  rw [← inner_verticalDirection_right, inner_gradient_verticalDirection]

theorem inner_point_zero_right {m : ℕ} (p : Space (m + 1)) (w : Space m) :
    inner ℝ p (point w 0) = inner ℝ (horizontal p) w := by
  conv_lhs => rw [← point_horizontal_last p]
  rw [inner_point_point]
  simp

theorem norm_sq_eq_horizontal_add_last_sq {m : ℕ} (p : Space (m + 1)) :
    ‖p‖ ^ 2 = ‖horizontal p‖ ^ 2 + p (Fin.last m) ^ 2 := by
  conv_lhs => rw [← point_horizontal_last p]
  rw [← real_inner_self_eq_norm_sq, inner_point_point, real_inner_self_eq_norm_sq]
  ring

theorem norm_gradient_sq_eq_horizontal_add_vertical_sq {m : ℕ}
    (v : Space (m + 1) → ℝ) (x : Space (m + 1)) :
    ‖gradient v x‖ ^ 2 = ‖horizontal (gradient v x)‖ ^ 2 + verticalDerivative v x ^ 2 := by
  rw [norm_sq_eq_horizontal_add_last_sq, gradient_last_eq_verticalDerivative]

theorem diffuseTiltDensity_vertical_eq {m : ℕ} (R : ℝ) (v : Space (m + 1) → ℝ)
    (x : Space (m + 1)) :
    diffuseTiltDensity R v (verticalDirection m) x = R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2 := by
  unfold diffuseTiltDensity
  rw [inner_gradient_verticalDirection, norm_gradient_sq_eq_horizontal_add_vertical_sq]
  ring

/-- At any differentiability point, the horizontal section gradient is the horizontal projection
of the ambient gradient. -/
theorem gradient_section_of_differentiableAt {m : ℕ} {v : Space (m + 1) → ℝ}
    {y : Space m} {t : ℝ} (hv : DifferentiableAt ℝ v (point y t)) :
    gradient (fun z ↦ v (point z t)) y = horizontal (gradient v (point y t)) := by
  have hp : HasFDerivAt (fun z : Space m ↦ point z t)
      (pointContinuousLinearMap.comp ((ContinuousLinearMap.id ℝ (Space m)).prod 0)) y :=
    pointContinuousLinearMap.hasFDerivAt.comp y
      ((hasFDerivAt_id y).prodMk (hasFDerivAt_const (𝕜 := ℝ) t y))
  have hd := hv.hasFDerivAt.comp y hp
  change HasFDerivAt (fun z ↦ v (point z t)) _ y at hd
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left, hd.fderiv]
  change fderiv ℝ v (point y t) (point w 0) = inner ℝ (horizontal (gradient v (point y t))) w
  rw [← inner_gradient_left, inner_point_zero_right]

/-- For any rotated, translated and dilated zero extension, the horizontal section gradient
agrees everywhere with the horizontal part of the totalized ambient gradient. -/
theorem Hypotheses.gradient_section_rescaled_isometry {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ)
    (c : Space (m + 1)) (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (y : Space m) (t : ℝ) :
    gradient (fun z ↦ zeroExtension g u (c + R • Q (point z t))) y =
      horizontal (gradient (fun x ↦ zeroExtension g u (c + R • Q x)) (point y t)) := by
  let v := fun x ↦ zeroExtension g u (c + R • Q x)
  by_cases hx : c + R • Q (point y t) ∈ epigraph g
  · have hu : ContDiffAt ℝ 2 u (c + R • Q (point y t)) :=
      h.solution_contDiffOn.contDiffAt ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
    have hU : DifferentiableAt ℝ (zeroExtension g u) (c + R • Q (point y t)) :=
      (hu.differentiableAt (by norm_num)).congr_of_eventuallyEq
        (zeroExtension_eventuallyEq h.graph_contDiff.continuous hx)
    have hv : DifferentiableAt ℝ v (point y t) :=
      hU.comp (point y t) (differentiableAt_const c |>.add
        ((Q.contDiff.differentiable_one (point y t)).const_smul R))
    exact gradient_section_of_differentiableAt hv
  · have hv0 : ∀ x, 0 ≤ v x := fun x ↦ h.zeroExtension_nonneg _
    have hz : v (point y t) = 0 := zeroExtension_of_notMem hx
    have hsec : gradient (fun z ↦ v (point z t)) y = 0 :=
      gradient_eq_zero_of_nonneg_zero (fun z ↦ hv0 (point z t)) hz
    have hamb : gradient v (point y t) = 0 := gradient_eq_zero_of_nonneg_zero hv0 hz
    simp [v, hsec, hamb, show horizontal (0 : Space (m + 1)) = 0 by ext i; simp [horizontal]]

/-! ### Rescaled Modica inequalities and rotated stress stationarity -/

/-- Pointwise consequence of the rescaled Modica bound: the horizontal gradient energy is
dominated by the excess `e_R - R⁻¹ * v_t²`. -/
theorem horizontal_gradient_sq_le_energy_sub_vertical_sq {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    {v : Space (m + 1) → ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x)
    (hmodica : ∀ x, (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 ≤ R * phasePotentialDensity f v x)
    (x : Space (m + 1)) :
    R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2 ≤
      rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2 := by
  rw [rescaledPhaseEnergyDensity_eq_kinetic_add_potential f R hv x]
  have hm := hmodica x
  have hkin : ‖gradient v x‖ ^ 2 / (2 * R) = (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 := by ring
  have h2 : R⁻¹ * ‖gradient v x‖ ^ 2 = 2 * ((2 * R)⁻¹ * ‖gradient v x‖ ^ 2) := by
    have hRne : R ≠ 0 := hR.ne'
    field_simp
  have hsplit := norm_gradient_sq_eq_horizontal_add_vertical_sq v x
  have hmul : R⁻¹ * ‖gradient v x‖ ^ 2 =
      R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2 + R⁻¹ * verticalDerivative v x ^ 2 := by
    rw [hsplit, mul_add]
  linarith

theorem energy_sub_vertical_sq_nonneg {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    {v : Space (m + 1) → ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x)
    (hmodica : ∀ x, (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 ≤ R * phasePotentialDensity f v x)
    (x : Space (m + 1)) :
    0 ≤ rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2 :=
  (mul_nonneg (inv_nonneg.mpr hR.le) (sq_nonneg _)).trans
    (horizontal_gradient_sq_le_energy_sub_vertical_sq hR hv hmodica x)

theorem energy_sub_vertical_sq_le_energy {m : ℕ} (f : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (v : Space (m + 1) → ℝ) (x : Space (m + 1)) :
    rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2 ≤
      rescaledPhaseEnergyDensity f R v x :=
  sub_le_self _ (mul_nonneg (inv_nonneg.mpr hR.le) (sq_nonneg _))

theorem rescaledPhaseEnergyDensity_le_two_mul_potential {d : ℕ} {f : ℝ → ℝ} {R : ℝ}
    {v : Space d → ℝ} (hv : ∀ x, 0 ≤ v x)
    (hmodica : ∀ x, (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 ≤ R * phasePotentialDensity f v x)
    (x : Space d) :
    rescaledPhaseEnergyDensity f R v x ≤ 2 * R * phasePotentialDensity f v x := by
  rw [rescaledPhaseEnergyDensity_eq_kinetic_add_potential f R hv x]
  have hkin : ‖gradient v x‖ ^ 2 / (2 * R) = (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 := by ring
  linarith [hmodica x]

/-- Rotated, translated and dilated Modica inequality on the whole ambient space. -/
theorem RigidityHypotheses.rescaled_isometry_modica_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (x : Space (m + 1)) :
    (2 * R)⁻¹ * ‖gradient (fun y ↦ zeroExtension g u (c + R • Q y)) x‖ ^ 2 ≤
      R * phasePotentialDensity f (fun y ↦ zeroExtension g u (c + R • Q y)) x := by
  by_cases hx : c + R • Q x ∈ epigraph g
  · have hp : 0 < zeroExtension g u (c + R • Q x) := (h.zeroExtension_pos_iff _).mpr hx
    rw [gradient_comp_translate_dilation_isometry, norm_smul, Q.symm.norm_map,
      Real.norm_of_nonneg hR.le, h.gradient_zeroExtension hx,
      phasePotentialDensity, indicator_of_mem (s := {y | 0 < zeroExtension g u (c + R • Q y)}) hp,
      zeroExtension_of_mem hx]
    have hm := mul_le_mul_of_nonneg_left (hr.modica_bound h hx) hR.le
    have hlhs : (2 * R)⁻¹ * (R * ‖gradient u (c + R • Q x)‖) ^ 2 =
        R * (‖gradient u (c + R • Q x)‖ ^ 2 / 2) := by
      field_simp
    rwa [hlhs]
  · have hp : ¬0 < zeroExtension g u (c + R • Q x) := by
      rw [zeroExtension_of_notMem hx]; exact lt_irrefl 0
    simp [gradient_comp_translate_dilation_isometry, h.gradient_zeroExtension_of_notMem hx,
      phasePotentialDensity, hp]

/-- Nonnegativity of `e_R - R⁻¹ * v_t²` for any rotated/translated rescaling of the solution. -/
theorem RigidityHypotheses.rescaled_isometry_energy_sub_vertical_sq_nonneg
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (x : Space (m + 1)) :
    0 ≤ rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • Q y)) x -
      R⁻¹ * verticalDerivative (fun y ↦ zeroExtension g u (c + R • Q y)) x ^ 2 :=
  energy_sub_vertical_sq_nonneg hR (fun _ ↦ h.zeroExtension_nonneg _)
    (hr.rescaled_isometry_modica_bound h c hR Q) x

/-- Pointwise horizontal section gradient bound by `e_R - R⁻¹ * v_t²` for any rotated/translated
rescaling of the solution. -/
theorem RigidityHypotheses.rescaled_isometry_section_gradient_sq_le
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (y : Space m) (t : ℝ) :
    R⁻¹ * ‖gradient (fun z ↦ zeroExtension g u (c + R • Q (point z t))) y‖ ^ 2 ≤
      rescaledPhaseEnergyDensity f R (fun x ↦ zeroExtension g u (c + R • Q x)) (point y t) -
        R⁻¹ * verticalDerivative (fun x ↦ zeroExtension g u (c + R • Q x)) (point y t) ^ 2 := by
  rw [h.gradient_section_rescaled_isometry c R Q y t]
  exact horizontal_gradient_sq_le_energy_sub_vertical_sq hR (fun _ ↦ h.zeroExtension_nonneg _)
    (hr.rescaled_isometry_modica_bound h c hR Q) (point y t)

/-- Spatial stress stationarity on the whole space for any rotated, translated and dilated
zero extension `v x := zeroExtension g u (c + R • Q x)`. -/
theorem RigidityHypotheses.rescaled_isometry_stress_stationarity
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {X : Space (m + 1) → Space (m + 1)} (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X) :
    (∫ x, (rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • Q y)) x *
        fieldDivergence basis X x -
      R⁻¹ * inner ℝ (gradient (fun y ↦ zeroExtension g u (c + R • Q y)) x)
        (fderiv ℝ X x (gradient (fun y ↦ zeroExtension g u (c + R • Q y)) x)))) = 0 := by
  let X₁ : Space (m + 1) → Space (m + 1) := fun w ↦ Q (X (Q.symm w))
  let Y : Space (m + 1) → Space (m + 1) := fun z ↦ X₁ (R⁻¹ • z)
  have hX₁ : ContDiff ℝ 1 X₁ := Q.contDiff.comp (hX.comp Q.symm.contDiff)
  have hY : ContDiff ℝ 1 Y := hX₁.comp (contDiff_id.const_smul R⁻¹)
  have hcX₁ : HasCompactSupport X₁ :=
    (hc.comp_homeomorph Q.symm.toHomeomorph).comp_left Q.map_zero
  have hcY : HasCompactSupport Y :=
    hcX₁.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))
  have hi := hr.translated_zeroExtension_stress_stationarity h basis c hY hcY
  let G : Space (m + 1) → ℝ := fun z ↦
    phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (c + y)) z * fieldDivergence basis Y z -
      inner ℝ (gradient (zeroExtension g u) (c + z))
        (fderiv ℝ Y z (gradient (zeroExtension g u) (c + z)))
  change (∫ z, G z) = 0 at hi
  have hsmul := Measure.integral_comp_smul G R (μ := volume)
  simp only [finrank_euclideanSpace_fin] at hsmul
  rw [hi, smul_zero] at hsmul
  have hrot := Q.measurePreserving.integral_comp Q.toHomeomorph.measurableEmbedding
    (fun w ↦ G (R • w))
  rw [← hrot] at hsmul
  have hpoint (x : Space (m + 1)) : G (R • Q x) =
      R⁻¹ ^ 2 * (rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • Q y)) x *
        fieldDivergence basis X x -
      R⁻¹ * inner ℝ (gradient (fun y ↦ zeroExtension g u (c + R • Q y)) x)
        (fderiv ℝ X x (gradient (fun y ↦ zeroExtension g u (c + R • Q y)) x))) := by
    have hfY : fderiv ℝ Y (R • Q x) = R⁻¹ • fderiv ℝ X₁ (Q x) := by
      dsimp only [Y]
      rw [fderiv_comp_smul, inv_smul_smul₀ hR.ne']
    have hdivY : fieldDivergence basis Y (R • Q x) = R⁻¹ * fieldDivergence basis X x := by
      have hd₁ : fieldDivergence basis X₁ (Q x) = fieldDivergence basis X x := by
        simpa only [X₁, Q.symm_symm, Q.symm_apply_apply] using
          fieldDivergence_isometry_conjugate basis Q.symm X (Q x)
      unfold fieldDivergence at hd₁ ⊢
      simp_rw [hfY, smul_apply, real_inner_smul_right, ← Finset.mul_sum]
      rw [hd₁]
    have hfX₁ (q : Space (m + 1)) : fderiv ℝ X₁ (Q x) q =
        Q (fderiv ℝ X x (Q.symm q)) := by
      have hd : fderiv ℝ X₁ (Q x) =
          (Q : Space (m + 1) →L[ℝ] Space (m + 1)).comp
            ((fderiv ℝ X (Q.symm (Q x))).comp (Q.symm : Space (m + 1) →L[ℝ] Space (m + 1))) := by
        change fderiv ℝ (Q ∘ (X ∘ Q.symm)) (Q x) = _
        rw [Q.comp_fderiv]
        congr 1
        exact Q.symm.toContinuousLinearEquiv.comp_right_fderiv
      rw [hd]
      simp only [ContinuousLinearMap.comp_apply, Q.symm_apply_apply]
      rfl
    have henergy : phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (c + y)) (R • Q x) =
        R⁻¹ * rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • Q y)) x := by
      rw [phaseEnergyDensity_comp_add_left,
        rescaledPhaseEnergyDensity_translate_dilation_isometry f _ c hR Q x]
      field_simp
    let q := gradient (zeroExtension g u) (c + R • Q x)
    have hQsymm : Q.symm q = R⁻¹ • gradient (fun y ↦ zeroExtension g u (c + R • Q y)) x := by
      rw [gradient_comp_translate_dilation_isometry _ c R Q x, inv_smul_smul₀ hR.ne']
    have hquad : inner ℝ q (fderiv ℝ Y (R • Q x) q) =
        R⁻¹ ^ 3 * inner ℝ (gradient (fun y ↦ zeroExtension g u (c + R • Q y)) x)
          (fderiv ℝ X x (gradient (fun y ↦ zeroExtension g u (c + R • Q y)) x)) := by
      have hinner : inner ℝ q (Q (fderiv ℝ X x (Q.symm q))) =
          inner ℝ (Q.symm q) (fderiv ℝ X x (Q.symm q)) := by
        rw [← Q.inner_map_map (Q.symm q), Q.apply_symm_apply]
      rw [hfY, smul_apply, hfX₁, real_inner_smul_right, hinner, hQsymm, map_smul,
        real_inner_smul_left, real_inner_smul_right]
      field_simp
    dsimp only [G]
    rw [henergy, hdivY]
    change R⁻¹ * rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • Q y)) x *
        (R⁻¹ * fieldDivergence basis X x) - inner ℝ q (fderiv ℝ Y (R • Q x) q) = _
    rw [hquad]
    ring
  simp_rw [hpoint] at hsmul
  rw [integral_const_mul] at hsmul
  exact (mul_eq_zero.mp hsmul).resolve_left (pow_ne_zero 2 (inv_ne_zero hR.ne'))

/-! ### Product-coordinate vertical vector fields, horizontal flux (FE4) and Caccioppoli (FE2) -/

theorem horizontalContinuousLinearMap_apply {m : ℕ} (x : Space (m + 1)) :
    horizontalContinuousLinearMap x = horizontal x := rfl

theorem contDiff_horizontal {m : ℕ} {n : WithTop ℕ∞} :
    ContDiff ℝ n (horizontal : Space (m + 1) → Space m) :=
  (horizontalContinuousLinearMap (m := m)).contDiff

theorem contDiff_last {m : ℕ} {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : Space (m + 1) ↦ x (Fin.last m)) :=
  (EuclideanSpace.proj (Fin.last m) : Space (m + 1) →L[ℝ] ℝ).contDiff

theorem continuous_last {m : ℕ} :
    Continuous (fun x : Space (m + 1) ↦ x (Fin.last m)) :=
  (EuclideanSpace.proj (Fin.last m) : Space (m + 1) →L[ℝ] ℝ).continuous

theorem measurable_verticalDerivative {m : ℕ} (v : Space (m + 1) → ℝ) :
    Measurable (verticalDerivative v) := by
  have heq : verticalDerivative v = fun x ↦ inner ℝ (gradient v x) (verticalDirection m) :=
    funext fun x ↦ (inner_gradient_verticalDirection v x).symm
  rw [heq]
  exact (measurable_gradient v).inner (𝕜 := ℝ) measurable_const

@[simp]
theorem horizontal_verticalDirection (m : ℕ) :
    horizontal (verticalDirection m) = 0 := by
  ext i
  simp [horizontal, verticalDirection]

@[simp]
theorem last_verticalDirection (m : ℕ) :
    verticalDirection m (Fin.last m) = 1 := by
  simp [verticalDirection]

/-- Product-coordinate functions `x ↦ α (horizontal x) * β (x (Fin.last m))` inherit compact
support from `α` and `β`. -/
theorem hasCompactSupport_mul_horizontal_last {m : ℕ} {α : Space m → ℝ} {β : ℝ → ℝ}
    (hα : HasCompactSupport α) (hβ : HasCompactSupport β) :
    HasCompactSupport (fun x : Space (m + 1) ↦ α (horizontal x) * β (x (Fin.last m))) := by
  obtain ⟨Rα, hRα⟩ := hα.isBounded.subset_closedBall (0 : Space m)
  obtain ⟨Rβ, hRβ⟩ := hβ.isBounded.subset_closedBall (0 : ℝ)
  let R := Real.sqrt (Rα ^ 2 + Rβ ^ 2)
  apply (isCompact_closedBall (0 : Space (m + 1)) R).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hne : α (horizontal x) * β (x (Fin.last m)) ≠ 0 := hx
  have hxα : horizontal x ∈ tsupport α :=
    subset_tsupport α (fun h0 ↦ hne (by simp [h0]))
  have hxβ : x (Fin.last m) ∈ tsupport β :=
    subset_tsupport β (fun h0 ↦ hne (by simp [h0]))
  have hnα : ‖horizontal x‖ ≤ Rα := by
    simpa only [mem_closedBall, dist_zero_right] using hRα hxα
  have hnβ : |x (Fin.last m)| ≤ Rβ := by
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hRβ hxβ
  have hsq : ‖x‖ ^ 2 ≤ Rα ^ 2 + Rβ ^ 2 := by
    rw [norm_sq_eq_horizontal_add_last_sq]
    have h1 : ‖horizontal x‖ ^ 2 ≤ Rα ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnα 2
    have h2 : x (Fin.last m) ^ 2 ≤ Rβ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hnβ 2
    linarith
  rw [mem_closedBall, dist_zero_right]
  exact Real.le_sqrt_of_sq_le hsq

/-- Directional derivative of a product-coordinate scalar `x ↦ α (horizontal x) * β (x_n)`. -/
theorem fderiv_mul_horizontal_last {m : ℕ} {α : Space m → ℝ} {β : ℝ → ℝ}
    (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 1 β) (x q : Space (m + 1)) :
    fderiv ℝ (fun z : Space (m + 1) ↦ α (horizontal z) * β (z (Fin.last m))) x q =
      β (x (Fin.last m)) * inner ℝ (gradient α (horizontal x)) (horizontal q) +
        α (horizontal x) * deriv β (x (Fin.last m)) * q (Fin.last m) := by
  have hdα : HasFDerivAt (fun z : Space (m + 1) ↦ α (horizontal z))
      ((fderiv ℝ α (horizontal x)).comp (horizontalContinuousLinearMap (m := m))) x :=
    (hα.differentiable_one (horizontal x)).hasFDerivAt.comp x
      (horizontalContinuousLinearMap (m := m)).hasFDerivAt
  have hdβ : HasFDerivAt (fun z : Space (m + 1) ↦ β (z (Fin.last m)))
      (deriv β (x (Fin.last m)) • (EuclideanSpace.proj (Fin.last m) : Space (m + 1) →L[ℝ] ℝ)) x := by
    have hc := (hβ.differentiable_one (x (Fin.last m))).hasDerivAt.comp_hasFDerivAt x
      (EuclideanSpace.proj (Fin.last m) : Space (m + 1) →L[ℝ] ℝ).hasFDerivAt
    exact hc
  have hmul := hdα.mul hdβ
  change HasFDerivAt (fun z : Space (m + 1) ↦ α (horizontal z) * β (z (Fin.last m))) _ x at hmul
  rw [hmul.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    horizontalContinuousLinearMap_apply, PiLp.proj_apply, smul_eq_mul,
    ← inner_gradient_left]
  ring

/-- Directional derivative of a vertical vector field `z ↦ a z • verticalDirection m`. -/
theorem fderiv_smul_verticalDirection {m : ℕ} {a : Space (m + 1) → ℝ} {x : Space (m + 1)}
    (ha : DifferentiableAt ℝ a x) (q : Space (m + 1)) :
    fderiv ℝ (fun z ↦ a z • verticalDirection m) x q =
      (fderiv ℝ a x q) • verticalDirection m := by
  rw [(ha.hasFDerivAt.smul_const (verticalDirection m)).fderiv]
  simp

/-- Divergence of a vertical vector field `z ↦ a z • verticalDirection m` in the standard basis. -/
theorem fieldDivergence_smul_verticalDirection {m : ℕ} {a : Space (m + 1) → ℝ}
    {x : Space (m + 1)} (ha : DifferentiableAt ℝ a x) :
    fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)
      (fun z ↦ a z • verticalDirection m) x = verticalDerivative a x := by
  let b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  change fieldDivergence b (fun z ↦ a z • verticalDirection m) x = verticalDerivative a x
  unfold fieldDivergence
  have hterm (i : Fin (m + 1)) :
      inner ℝ (b i) (fderiv ℝ (fun z ↦ a z • verticalDirection m) x (b i)) =
        if i = Fin.last m then fderiv ℝ a x (b (Fin.last m)) else 0 := by
    rw [fderiv_smul_verticalDirection ha (b i), real_inner_smul_right,
      inner_verticalDirection_right]
    have hb : (b i) (Fin.last m) = if i = Fin.last m then 1 else 0 := by
      simp [b, EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]
    rw [hb]
    split_ifs with hi
    · subst hi; ring
    · ring
  rw [Finset.sum_congr rfl (fun i _ ↦ hterm i), Finset.sum_ite_eq' Finset.univ (Fin.last m)]
  simp only [Finset.mem_univ, ↓reduceIte]
  have hblast : b (Fin.last m) = verticalDirection m := by
    ext j
    simp [b, verticalDirection, EuclideanSpace.basisFun_apply]
  rw [hblast]
  rfl

/-- Horizontal normal-flux identity (FE4.1) for any nonnegative locally Lipschitz function `v`
with integrable rescaled energy satisfying whole-space stress stationarity:
`∫ R⁻¹ * ψ(x_n) * v_t(x) * ⟨∇_y v(x), ∇φ(y)⟩ = ∫ φ(y) * ψ'(x_n) * (e_R(x) - R⁻¹ * v_t(x)²)`. -/
theorem rescaled_horizontal_flux_identity {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    {v : Space (m + 1) → ℝ} (hv_lip : LocallyLipschitz v)
    (hiE : ∀ K : Set (Space (m + 1)), IsCompact K →
      IntegrableOn (rescaledPhaseEnergyDensity f R v) K)
    (hstress : ∀ X : Space (m + 1) → Space (m + 1), ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x, (rescaledPhaseEnergyDensity f R v x *
          fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) X x -
        R⁻¹ * inner ℝ (gradient v x) (fderiv ℝ X x (gradient v x)))) = 0)
    {φ : Space m → ℝ} {ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, R⁻¹ * ψ (x (Fin.last m)) * verticalDerivative v x *
        inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x))) =
      ∫ x, φ (horizontal x) * deriv ψ (x (Fin.last m)) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) := by
  let basis := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  let a : Space (m + 1) → ℝ := fun x ↦ φ (horizontal x) * ψ (x (Fin.last m))
  let X : Space (m + 1) → Space (m + 1) := fun x ↦ a x • verticalDirection m
  have ha : ContDiff ℝ 1 a := (hφ.comp contDiff_horizontal).mul (hψ.comp contDiff_last)
  have hca : HasCompactSupport a := hasCompactSupport_mul_horizontal_last hcφ hcψ
  have hX : ContDiff ℝ 1 X := ha.smul contDiff_const
  have hcX : HasCompactSupport X := hca.smul_right
  have hst := hstress X hX hcX
  change (∫ x, (rescaledPhaseEnergyDensity f R v x * fieldDivergence basis X x -
    R⁻¹ * inner ℝ (gradient v x) (fderiv ℝ X x (gradient v x)))) = 0 at hst
  have hpt (x : Space (m + 1)) :
      rescaledPhaseEnergyDensity f R v x * fieldDivergence basis X x -
          R⁻¹ * inner ℝ (gradient v x) (fderiv ℝ X x (gradient v x)) =
        φ (horizontal x) * deriv ψ (x (Fin.last m)) *
            (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) -
          R⁻¹ * ψ (x (Fin.last m)) * verticalDerivative v x *
            inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x)) := by
    have hdiv : fieldDivergence basis X x = φ (horizontal x) * deriv ψ (x (Fin.last m)) := by
      rw [fieldDivergence_smul_verticalDirection (ha.differentiable_one x)]
      change fderiv ℝ a x (verticalDirection m) = _
      rw [fderiv_mul_horizontal_last hφ hψ x (verticalDirection m)]
      simp
    have hquad : inner ℝ (gradient v x) (fderiv ℝ X x (gradient v x)) =
        ψ (x (Fin.last m)) * verticalDerivative v x *
            inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x)) +
          φ (horizontal x) * deriv ψ (x (Fin.last m)) * verticalDerivative v x ^ 2 := by
      rw [fderiv_smul_verticalDirection (ha.differentiable_one x) (gradient v x),
        real_inner_smul_right, inner_gradient_verticalDirection,
        fderiv_mul_horizontal_last hφ hψ x (gradient v x),
        gradient_last_eq_verticalDerivative]
      have hcomm : inner ℝ (gradient φ (horizontal x)) (horizontal (gradient v x)) =
          inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x)) :=
        real_inner_comm _ _
      rw [hcomm]
      ring
    rw [hdiv, hquad]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt)] at hst
  let K := tsupport a ∪ (tsupport fun x : Space (m + 1) ↦
    φ (horizontal x) * deriv ψ (x (Fin.last m)))
  have hψ' : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hcψ' : HasCompactSupport (deriv ψ) := hcψ.deriv
  have hc_aphi : HasCompactSupport (fun x : Space (m + 1) ↦
      φ (horizontal x) * deriv ψ (x (Fin.last m))) :=
    hasCompactSupport_mul_horizontal_last hcφ hcψ'
  have hK : IsCompact K := hca.union hc_aphi
  obtain ⟨Cg, hCg⟩ := gradient_bound_of_locallyLipschitz hv_lip hK
  have hgradφ_cont : Continuous (gradient φ) :=
    (toDual ℝ (Space m)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hc_lhs : HasCompactSupport (fun x : Space (m + 1) ↦
      ψ (x (Fin.last m)) • gradient φ (horizontal x)) := by
    have hcgφ : HasCompactSupport (gradient φ) := by
      apply hcφ.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ (isClosed_tsupport φ)
      intro y hy; by_contra hn
      exact hy (by simp [gradient, fderiv_of_notMem_tsupport ℝ hn])
    obtain ⟨R1, hR1⟩ := hcgφ.isBounded.subset_closedBall (0 : Space m)
    obtain ⟨R2, hR2⟩ := hcψ.isBounded.subset_closedBall (0 : ℝ)
    apply (isCompact_closedBall (0 : Space (m + 1)) (Real.sqrt (R1 ^ 2 + R2 ^ 2))).of_isClosed_subset
      (isClosed_tsupport _)
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    have hx1 : horizontal x ∈ tsupport (gradient φ) :=
      subset_tsupport _ (fun h0 ↦ hx (by simp [h0]))
    have hx2 : x (Fin.last m) ∈ tsupport ψ :=
      subset_tsupport _ (fun h0 ↦ hx (by simp [h0]))
    have hn1 : ‖horizontal x‖ ≤ R1 := by simpa [mem_closedBall, dist_zero_right] using hR1 hx1
    have hn2 : |x (Fin.last m)| ≤ R2 := by
      simpa [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hR2 hx2
    rw [mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    rw [norm_sq_eq_horizontal_add_last_sq]
    have hs1 : ‖horizontal x‖ ^ 2 ≤ R1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn1 2
    have hs2 : x (Fin.last m) ^ 2 ≤ R2 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hn2 2
    linarith
  let K2 := K ∪ tsupport (fun x : Space (m + 1) ↦ ψ (x (Fin.last m)) • gradient φ (horizontal x))
  have hK2 : IsCompact K2 := hK.union hc_lhs
  obtain ⟨Cg2, hCg2⟩ := gradient_bound_of_locallyLipschitz hv_lip hK2
  have hi_rhs : Integrable (fun x : Space (m + 1) ↦
      φ (horizontal x) * deriv ψ (x (Fin.last m)) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) := by
    have hc_fac : Continuous (fun x : Space (m + 1) ↦
        φ (horizontal x) * deriv ψ (x (Fin.last m))) :=
      (hφ.continuous.comp continuous_horizontal).mul (hψ'.comp continuous_last)
    have hi1 : IntegrableOn (rescaledPhaseEnergyDensity f R v) K2 := hiE K2 hK2
    have hi2 : IntegrableOn (fun x ↦ R⁻¹ * verticalDerivative v x ^ 2) K2 := by
      apply (continuousOn_const.integrableOn_compact hK2
        (f := fun _ ↦ |R⁻¹| * (Cg2 : ℝ) ^ 2)).mono'
        (measurable_const.mul ((measurable_verticalDerivative v).pow_const 2)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hK2.measurableSet] with x hx
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_eq_abs, norm_pow, ← inner_gradient_verticalDirection]
      have hvt : ‖inner ℝ (gradient v x) (verticalDirection m)‖ ≤ Cg2 := by
        calc
          ‖inner ℝ (gradient v x) (verticalDirection m)‖ ≤
              ‖gradient v x‖ * ‖verticalDirection m‖ := norm_inner_le_norm _ _
          _ = ‖gradient v x‖ := by rw [norm_verticalDirection, mul_one]
          _ ≤ Cg2 := hCg2 x hx
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hvt 2) (abs_nonneg _)
    have hiK : IntegrableOn (fun x : Space (m + 1) ↦
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) *
          (φ (horizontal x) * deriv ψ (x (Fin.last m)))) K2 :=
      (hi1.sub hi2).mul_continuousOn hc_fac.continuousOn hK2
    exact (hiK.congr_fun (fun x _ ↦ by dsimp only; ring) hK2.measurableSet)
      |>.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
        have hn : x ∉ tsupport (fun z : Space (m + 1) ↦
            φ (horizontal z) * deriv ψ (z (Fin.last m))) :=
          fun hh ↦ hx (Or.inl (Or.inr hh))
        have hz : φ (horizontal x) * deriv ψ (x (Fin.last m)) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun z : Space (m + 1) ↦ φ (horizontal z) * deriv ψ (z (Fin.last m))) hn
        simp [hz])
  have hi_lhs : Integrable (fun x : Space (m + 1) ↦
      R⁻¹ * ψ (x (Fin.last m)) * verticalDerivative v x *
        inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x))) := by
    have hc_psi : Continuous (fun x : Space (m + 1) ↦ ψ (x (Fin.last m))) :=
      hψ.continuous.comp continuous_last
    have hc_gphi : Continuous (fun x : Space (m + 1) ↦ gradient φ (horizontal x)) :=
      hgradφ_cont.comp continuous_horizontal
    obtain ⟨Mψ, hMψ⟩ := hcψ.exists_bound_of_continuous hψ.continuous
    obtain ⟨Mgφ, hMgφ⟩ := hK2.exists_bound_of_continuousOn hc_gphi.continuousOn
    have hm_vt : Measurable (verticalDerivative v) := measurable_verticalDerivative v
    have hm_hg : Measurable (fun x : Space (m + 1) ↦ horizontal (gradient v x)) :=
      continuous_horizontal.measurable.comp (measurable_gradient v)
    have hiK : IntegrableOn (fun x : Space (m + 1) ↦
        R⁻¹ * ψ (x (Fin.last m)) * verticalDerivative v x *
          inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x))) K2 := by
      apply (continuousOn_const.integrableOn_compact hK2
        (f := fun _ ↦ |R⁻¹| * |Mψ| * (Cg2 : ℝ) * ((Cg2 : ℝ) * |Mgφ|))).mono'
        (((measurable_const.mul hc_psi.measurable).mul hm_vt).mul
          (hm_hg.inner (𝕜 := ℝ) hc_gphi.measurable)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hK2.measurableSet] with x hx
      have hvt : ‖verticalDerivative v x‖ ≤ Cg2 := by
        rw [← inner_gradient_verticalDirection]
        exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (by rw [norm_verticalDirection, mul_one]; exact hCg2 x hx)
      have hhg : ‖horizontal (gradient v x)‖ ≤ Cg2 := by
        have hsq := norm_sq_eq_horizontal_add_last_sq (gradient v x)
        have hle : ‖horizontal (gradient v x)‖ ^ 2 ≤ ‖gradient v x‖ ^ 2 := by linarith [sq_nonneg (gradient v x (Fin.last m))]
        exact ( nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
          (by simpa only [sq] using hle) ).trans (hCg2 x hx)
      have hin : ‖inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x))‖ ≤
          (Cg2 : ℝ) * |Mgφ| :=
        (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul hhg ((hMgφ x hx).trans (le_abs_self Mgφ)) (norm_nonneg _) Cg2.coe_nonneg)
      simp only [Pi.mul_apply]
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs R⁻¹]
      exact mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left ((hMψ _).trans (le_abs_self Mψ)) (abs_nonneg _))
          hvt (norm_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        hin (norm_nonneg _)
        (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) Cg2.coe_nonneg)
    exact hiK.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      have hn : x ∉ tsupport (fun z : Space (m + 1) ↦
          ψ (z (Fin.last m)) • gradient φ (horizontal z)) :=
        fun hh ↦ hx (Or.inr hh)
      have hzero : ψ (x (Fin.last m)) • gradient φ (horizontal x) = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun z : Space (m + 1) ↦ ψ (z (Fin.last m)) • gradient φ (horizontal z)) hn
      rcases smul_eq_zero.mp hzero with hψ0 | hg0
      · simp [hψ0]
      · simp [hg0])
  rw [integral_sub hi_rhs hi_lhs] at hst
  linarith

/-- Horizontal normal-flux boundary cutoff bound (FE4.2). -/
theorem rescaled_horizontal_flux_bound {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    {v : Space (m + 1) → ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hv_lip : LocallyLipschitz v)
    (hmodica : ∀ x, (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 ≤ R * phasePotentialDensity f v x)
    (hiE : ∀ K : Set (Space (m + 1)), IsCompact K →
      IntegrableOn (rescaledPhaseEnergyDensity f R v) K)
    (hstress : ∀ X : Space (m + 1) → Space (m + 1), ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x, (rescaledPhaseEnergyDensity f R v x *
          fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) X x -
        R⁻¹ * inner ℝ (gradient v x) (fderiv ℝ X x (gradient v x)))) = 0)
    {φ : Space m → ℝ} {ψ : ℝ → ℝ} {Mφ : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (hMφ : ∀ y, |φ y| ≤ Mφ)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    |∫ x, R⁻¹ * ψ (x (Fin.last m)) * verticalDerivative v x *
        inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x))| ≤
      Mφ * ∫ x in {z | horizontal z ∈ tsupport φ ∧ z (Fin.last m) ∈ tsupport (deriv ψ)},
        |deriv ψ (x (Fin.last m))| * rescaledPhaseEnergyDensity f R v x := by
  have hMφ0 : 0 ≤ Mφ := (abs_nonneg (φ 0)).trans (hMφ 0)
  rw [rescaled_horizontal_flux_identity hv_lip hiE hstress hφ hcφ hψ hcψ, ← Real.norm_eq_abs]
  let S : Set (Space (m + 1)) :=
    {z | horizontal z ∈ tsupport φ ∧ z (Fin.last m) ∈ tsupport (deriv ψ)}
  have hS_closed : IsClosed S :=
    ((isClosed_tsupport φ).preimage continuous_horizontal).inter
      ((isClosed_tsupport (deriv ψ)).preimage continuous_last)
  have hS_comp : IsCompact S := by
    obtain ⟨R1, hR1⟩ := hcφ.isBounded.subset_closedBall (0 : Space m)
    obtain ⟨R2, hR2⟩ := hcψ.deriv.isBounded.subset_closedBall (0 : ℝ)
    apply (isCompact_closedBall (0 : Space (m + 1)) (Real.sqrt (R1 ^ 2 + R2 ^ 2))).of_isClosed_subset
      hS_closed
    intro x hx
    have hn1 : ‖horizontal x‖ ≤ R1 := by simpa [mem_closedBall, dist_zero_right] using hR1 hx.1
    have hn2 : |x (Fin.last m)| ≤ R2 := by
      simpa [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hR2 hx.2
    rw [mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    rw [norm_sq_eq_horizontal_add_last_sq]
    have hs1 : ‖horizontal x‖ ^ 2 ≤ R1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn1 2
    have hs2 : x (Fin.last m) ^ 2 ≤ R2 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hn2 2
    linarith
  have hcut : (∫ x, φ (horizontal x) * deriv ψ (x (Fin.last m)) *
      (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) =
      ∫ x in S, φ (horizontal x) * deriv ψ (x (Fin.last m)) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_cases hx1 : horizontal x ∈ tsupport φ
    · have hx2 : x (Fin.last m) ∉ tsupport (deriv ψ) := fun hh ↦ hx ⟨hx1, hh⟩
      simp [image_eq_zero_of_notMem_tsupport hx2]
    · simp [image_eq_zero_of_notMem_tsupport hx1]
  rw [hcut]
  have hψ' : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  obtain ⟨Cg, hCg⟩ := gradient_bound_of_locallyLipschitz hv_lip hS_comp
  have hi_vt : IntegrableOn (fun x ↦ R⁻¹ * verticalDerivative v x ^ 2) S := by
    apply (continuousOn_const.integrableOn_compact hS_comp
      (f := fun _ ↦ |R⁻¹| * (Cg : ℝ) ^ 2)).mono'
      (measurable_const.mul ((measurable_verticalDerivative v).pow_const 2)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hS_comp.measurableSet] with x hx
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, norm_pow, ← inner_gradient_verticalDirection]
    have hvt : ‖inner ℝ (gradient v x) (verticalDirection m)‖ ≤ Cg :=
      (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (by rw [norm_verticalDirection, mul_one]; exact hCg x hx)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hvt 2) (abs_nonneg _)
  have hi_lhs : IntegrableOn (fun x ↦ φ (horizontal x) * deriv ψ (x (Fin.last m)) *
      (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) S := by
    have hc_fac : Continuous (fun x : Space (m + 1) ↦ φ (horizontal x) * deriv ψ (x (Fin.last m))) :=
      (hφ.continuous.comp continuous_horizontal).mul (hψ'.comp continuous_last)
    exact (((hiE S hS_comp).sub hi_vt).mul_continuousOn hc_fac.continuousOn hS_comp).congr_fun
      (fun x _ ↦ by simp only [Pi.sub_apply]; ring) hS_comp.measurableSet
  have hi_rhs : IntegrableOn (fun x ↦ Mφ * (|deriv ψ (x (Fin.last m))| *
      rescaledPhaseEnergyDensity f R v x)) S := by
    have hc_abs : Continuous (fun x : Space (m + 1) ↦ Mφ * |deriv ψ (x (Fin.last m))|) :=
      continuous_const.mul ((hψ'.comp continuous_last).abs)
    exact ((hiE S hS_comp).mul_continuousOn hc_abs.continuousOn hS_comp).congr_fun
      (fun x _ ↦ by dsimp only; ring) hS_comp.measurableSet
  calc
    ‖∫ x in S, φ (horizontal x) * deriv ψ (x (Fin.last m)) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)‖ ≤
      ∫ x in S, ‖φ (horizontal x) * deriv ψ (x (Fin.last m)) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in S, Mφ * (|deriv ψ (x (Fin.last m))| * rescaledPhaseEnergyDensity f R v x) := by
      apply setIntegral_mono_on hi_lhs.norm hi_rhs hS_comp.measurableSet
      intro x _
      have hA0 := energy_sub_vertical_sq_nonneg hR hv hmodica x
      have hAe := energy_sub_vertical_sq_le_energy f hR v x
      have hE0 : 0 ≤ rescaledPhaseEnergyDensity f R v x := hA0.trans hAe
      dsimp only
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hA0]
      calc
        |φ (horizontal x)| * |deriv ψ (x (Fin.last m))| *
            (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) ≤
          (Mφ * |deriv ψ (x (Fin.last m))|) * rescaledPhaseEnergyDensity f R v x :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hMφ _) (abs_nonneg _)) hAe hA0
            (mul_nonneg hMφ0 (abs_nonneg _))
        _ = Mφ * (|deriv ψ (x (Fin.last m))| * rescaledPhaseEnergyDensity f R v x) := by ring
    _ = Mφ * ∫ x in S, |deriv ψ (x (Fin.last m))| * rescaledPhaseEnergyDensity f R v x :=
      integral_const_mul _ _

/-- Localized height stress identity (FE2 exact identity) obtained by testing whole-space stress
stationarity against `X(y, t) = φ(y)² ψ(t)² (t - lam) e_n`. -/
theorem rescaled_height_stress_identity {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    {v : Space (m + 1) → ℝ} (hv_lip : LocallyLipschitz v)
    (hiE : ∀ K : Set (Space (m + 1)), IsCompact K →
      IntegrableOn (rescaledPhaseEnergyDensity f R v) K)
    (hstress : ∀ X : Space (m + 1) → Space (m + 1), ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x, (rescaledPhaseEnergyDensity f R v x *
          fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) X x -
        R⁻¹ * inner ℝ (gradient v x) (fderiv ℝ X x (gradient v x)))) = 0)
    {φ : Space m → ℝ} {ψ : ℝ → ℝ} (lam : ℝ)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) =
      2 * (∫ x, φ (horizontal x) * ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) *
          R⁻¹ * verticalDerivative v x *
            inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x))) -
        2 * ∫ x, φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
          (x (Fin.last m) - lam) *
          (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) := by
  let α : Space m → ℝ := fun y ↦ φ y ^ 2
  let β : ℝ → ℝ := fun t ↦ ψ t ^ 2 * (t - lam)
  have hα : ContDiff ℝ 1 α := hφ.pow 2
  have hcα : HasCompactSupport α := by
    apply hcφ.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport φ)
    intro y hy
    exact subset_tsupport φ (fun h0 ↦ hy (by simp [α, h0]))
  have hβ : ContDiff ℝ 1 β := (hψ.pow 2).mul (contDiff_id.sub contDiff_const)
  have hcβ : HasCompactSupport β := by
    apply hcψ.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro t ht
    exact subset_tsupport ψ (fun h0 ↦ ht (by simp [β, h0]))
  have hflux := rescaled_horizontal_flux_identity hv_lip hiE hstress hα hcα hβ hcβ
  have hgrad_α (y : Space m) : gradient α y = (2 * φ y) • gradient φ y := by
    apply ext_inner_right ℝ
    intro w
    rw [inner_gradient_left, ((hφ.differentiable_one y).hasFDerivAt.pow 2).fderiv,
      smul_apply, real_inner_smul_left, inner_gradient_left]
    simp only [Nat.add_one_sub_one, pow_one, smul_eq_mul]
    ring
  have hderiv_β (t : ℝ) : deriv β t = ψ t ^ 2 + 2 * ψ t * deriv ψ t * (t - lam) := by
    have hd1 : HasDerivAt (fun s ↦ ψ s ^ 2) (2 * ψ t ^ (2 - 1) * deriv ψ t) t :=
      (hψ.differentiable_one t).hasDerivAt.pow 2
    have hd2 : HasDerivAt (fun s ↦ s - lam) 1 t := by
      simpa using (hasDerivAt_id t).sub_const lam
    have hd := hd1.mul hd2
    change HasDerivAt β _ t at hd
    rw [hd.deriv]
    ring
  have hlhs_eq : (∫ x, R⁻¹ * β (x (Fin.last m)) * verticalDerivative v x *
      inner ℝ (horizontal (gradient v x)) (gradient α (horizontal x))) =
      2 * ∫ x, φ (horizontal x) * ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) *
        R⁻¹ * verticalDerivative v x *
          inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine Eventually.of_forall (fun x ↦ ?_)
    dsimp only [β]
    rw [hgrad_α, real_inner_smul_right]
    ring
  let K := tsupport (fun x : Space (m + 1) ↦ φ (horizontal x) * ψ (x (Fin.last m)))
  have hc_φψ : HasCompactSupport (fun x : Space (m + 1) ↦ φ (horizontal x) * ψ (x (Fin.last m))) :=
    hasCompactSupport_mul_horizontal_last hcφ hcψ
  have hK : IsCompact K := hc_φψ
  obtain ⟨Cg, hCg⟩ := gradient_bound_of_locallyLipschitz hv_lip hK
  have hi_A : IntegrableOn
      (fun x ↦ rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) K := by
    refine (hiE K hK).sub ?_
    apply (continuousOn_const.integrableOn_compact hK
      (f := fun _ ↦ |R⁻¹| * (Cg : ℝ) ^ 2)).mono'
      (measurable_const.mul ((measurable_verticalDerivative v).pow_const 2)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, norm_pow, ← inner_gradient_verticalDirection]
    have hvt : ‖inner ℝ (gradient v x) (verticalDirection m)‖ ≤ Cg :=
      (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (by rw [norm_verticalDirection, mul_one]; exact hCg x hx)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hvt 2) (abs_nonneg _)
  have hi1 : Integrable (fun x : Space (m + 1) ↦
      φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) := by
    have hc1 : Continuous (fun x : Space (m + 1) ↦
        φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2) :=
      ((hφ.continuous.comp continuous_horizontal).pow 2).mul
        ((hψ.continuous.comp continuous_last).pow 2)
    exact ((hi_A.mul_continuousOn hc1.continuousOn hK).congr_fun
      (fun x _ ↦ by dsimp only; ring) hK.measurableSet).integrable_of_forall_notMem_eq_zero
      (fun x hx ↦ by
        have hz : φ (horizontal x) * ψ (x (Fin.last m)) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun z : Space (m + 1) ↦ φ (horizontal z) * ψ (z (Fin.last m))) hx
        rcases mul_eq_zero.mp hz with h0 | h0 <;> simp [h0])
  have hi2 : Integrable (fun x : Space (m + 1) ↦
      2 * (φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
        (x (Fin.last m) - lam) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2))) := by
    have hψ' : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
    have hc2 : Continuous (fun x : Space (m + 1) ↦
        2 * (φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
          (x (Fin.last m) - lam))) :=
      continuous_const.mul (((((hφ.continuous.comp continuous_horizontal).pow 2).mul
        (hψ.continuous.comp continuous_last)).mul
        (hψ'.comp continuous_last)).mul
        (continuous_last.sub continuous_const))
    exact ((hi_A.mul_continuousOn hc2.continuousOn hK).congr_fun
      (fun x _ ↦ by dsimp only; ring) hK.measurableSet).integrable_of_forall_notMem_eq_zero
      (fun x hx ↦ by
        have hz : φ (horizontal x) * ψ (x (Fin.last m)) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun z : Space (m + 1) ↦ φ (horizontal z) * ψ (z (Fin.last m))) hx
        rcases mul_eq_zero.mp hz with h0 | h0 <;> simp [h0])
  have hrhs_eq : (∫ x, α (horizontal x) * deriv β (x (Fin.last m)) *
      (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) =
      (∫ x, φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) +
      2 * ∫ x, φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
        (x (Fin.last m) - lam) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) := by
    have hcongr : (∫ x, α (horizontal x) * deriv β (x (Fin.last m)) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) =
        ∫ x, (φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
          (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) +
          2 * (φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
            (x (Fin.last m) - lam) *
            (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2))) := by
      apply integral_congr_ae
      refine Eventually.of_forall (fun x ↦ ?_)
      dsimp only [α]
      rw [hderiv_β]
      ring
    have hadd := integral_add hi1 hi2
    rw [hcongr, hadd, integral_const_mul]
  rw [hlhs_eq, hrhs_eq] at hflux
  linarith

private theorem height_caccioppoli_cross_pointwise
    {φx ψt dt R_inv vt inn nhg ngφ A : ℝ}
    (hR_inv : 0 ≤ R_inv) (hinn : |inn| ≤ nhg * ngφ) (hmod : R_inv * nhg ^ 2 ≤ A) :
    2 * (φx * ψt ^ 2 * dt * R_inv * vt * inn) ≤
      (1 / 2) * (φx ^ 2 * ψt ^ 2 * A) + 2 * (ψt ^ 2 * dt ^ 2 * R_inv * vt ^ 2 * ngφ ^ 2) := by
  let a := |φx| * nhg
  let b := |vt| * ngφ * |dt|
  have hab : 2 * (a * b) ≤ (1 / 2) * a ^ 2 + 2 * b ^ 2 := by
    linarith [sq_nonneg (a - 2 * b)]
  have ha2 : a ^ 2 = φx ^ 2 * nhg ^ 2 := by dsimp only [a]; rw [mul_pow, sq_abs]
  have hb2 : b ^ 2 = vt ^ 2 * ngφ ^ 2 * dt ^ 2 := by
    dsimp only [b]; rw [mul_pow, mul_pow, sq_abs, sq_abs]
  have hprod : φx * dt * vt * inn ≤ a * b := by
    calc
      φx * dt * vt * inn ≤ |φx * dt * vt * inn| := le_abs_self _
      _ = (|φx| * |dt| * |vt|) * |inn| := by simp only [abs_mul]
      _ ≤ (|φx| * |dt| * |vt|) * (nhg * ngφ) :=
        mul_le_mul_of_nonneg_left hinn (by positivity)
      _ = a * b := by dsimp only [a, b]; ring
  have hw : 0 ≤ ψt ^ 2 * R_inv := mul_nonneg (sq_nonneg _) hR_inv
  have h1 : 2 * (φx * ψt ^ 2 * dt * R_inv * vt * inn) ≤
      (ψt ^ 2 * R_inv) * (2 * (a * b)) := by
    calc
      2 * (φx * ψt ^ 2 * dt * R_inv * vt * inn) =
          (ψt ^ 2 * R_inv) * (2 * (φx * dt * vt * inn)) := by ring
      _ ≤ (ψt ^ 2 * R_inv) * (2 * (a * b)) :=
        mul_le_mul_of_nonneg_left (by linarith) hw
  have h2 := mul_le_mul_of_nonneg_left hab hw
  rw [ha2, hb2] at h2
  have h3 : (1 / 2) * (φx ^ 2 * ψt ^ 2 * (R_inv * nhg ^ 2)) ≤
      (1 / 2) * (φx ^ 2 * ψt ^ 2 * A) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmod (mul_nonneg (sq_nonneg _) (sq_nonneg _))) (by norm_num)
  linarith [h1.trans h2, h3]

private theorem integrable_mul_continuous_of_tsupport_subset {d : ℕ}
    {w g : Space d → ℝ} {K : Set (Space d)} (hK : IsCompact K)
    (hw : Continuous w) (hg : IntegrableOn g K) (hzero : ∀ x, x ∉ K → w x = 0) :
    Integrable (fun x ↦ w x * g x) :=
  ((hg.mul_continuousOn hw.continuousOn hK).congr_fun
    (fun x _ ↦ mul_comm _ _) hK.measurableSet).integrable_of_forall_notMem_eq_zero
    (fun x hx ↦ by simp [hzero x hx])

/-- One-phase localized height Caccioppoli inequality with explicit boundary error (FE2.2), in its
strong excess form controlling `∫ φ² ψ² (e_R - R⁻¹ * v_t²)` (and hence `∫ φ² ψ² R⁻¹ ‖∇_y v‖²`). -/
theorem rescaled_height_excess_caccioppoli {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    {v : Space (m + 1) → ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hv_lip : LocallyLipschitz v)
    (hmodica : ∀ x, (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 ≤ R * phasePotentialDensity f v x)
    (hiE : ∀ K : Set (Space (m + 1)), IsCompact K →
      IntegrableOn (rescaledPhaseEnergyDensity f R v) K)
    (hstress : ∀ X : Space (m + 1) → Space (m + 1), ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x, (rescaledPhaseEnergyDensity f R v x *
          fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) X x -
        R⁻¹ * inner ℝ (gradient v x) (fderiv ℝ X x (gradient v x)))) = 0)
    {φ : Space m → ℝ} {ψ : ℝ → ℝ} (lam : ℝ)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) ≤
      4 * (∫ x, ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) ^ 2 *
          R⁻¹ * verticalDerivative v x ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2) +
        4 * ∫ x, φ (horizontal x) ^ 2 *
          |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - lam)| *
          rescaledPhaseEnergyDensity f R v x := by
  have hid := rescaled_height_stress_identity hv_lip hiE hstress lam hφ hcφ hψ hcψ
  have hgradφ_cont : Continuous (gradient φ) :=
    (toDual ℝ (Space m)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hcgφ : HasCompactSupport (gradient φ) := by
    apply hcφ.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport φ)
    intro y hy; by_contra hn
    exact hy (by simp [gradient, fderiv_of_notMem_tsupport ℝ hn])
  obtain ⟨Rφ, hRφ⟩ := hcφ.isBounded.subset_closedBall (0 : Space m)
  obtain ⟨Rg, hRg⟩ := hcgφ.isBounded.subset_closedBall (0 : Space m)
  obtain ⟨Rψ, hRψ⟩ := hcψ.isBounded.subset_closedBall (0 : ℝ)
  let R0 : ℝ := Real.sqrt (max Rφ Rg ^ 2 + Rψ ^ 2) + 1
  let K : Set (Space (m + 1)) := closedBall 0 R0
  have hK : IsCompact K := isCompact_closedBall 0 R0
  have hmem_K_of_φψ {x : Space (m + 1)} (h1 : φ (horizontal x) ≠ 0) (h2 : ψ (x (Fin.last m)) ≠ 0) :
      x ∈ K := by
    have hn1 : ‖horizontal x‖ ≤ max Rφ Rg :=
      (by simpa [mem_closedBall, dist_zero_right] using hRφ (subset_tsupport φ h1) :
        ‖horizontal x‖ ≤ Rφ).trans (le_max_left _ _)
    have hn2 : |x (Fin.last m)| ≤ Rψ := by
      simpa [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hRψ (subset_tsupport ψ h2)
    have hmax0 : 0 ≤ max Rφ Rg := (norm_nonneg (horizontal x)).trans hn1
    have hsq : ‖x‖ ^ 2 ≤ max Rφ Rg ^ 2 + Rψ ^ 2 := by
      rw [norm_sq_eq_horizontal_add_last_sq]
      have hs1 : ‖horizontal x‖ ^ 2 ≤ max Rφ Rg ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn1 2
      have hs2 : x (Fin.last m) ^ 2 ≤ Rψ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hn2 2
      linarith
    rw [mem_closedBall, dist_zero_right]
    linarith [Real.le_sqrt_of_sq_le hsq]
  have hmem_K_of_gφψ {x : Space (m + 1)}
      (h1 : gradient φ (horizontal x) ≠ 0) (h2 : ψ (x (Fin.last m)) ≠ 0) : x ∈ K := by
    have hn1 : ‖horizontal x‖ ≤ max Rφ Rg :=
      (by simpa [mem_closedBall, dist_zero_right] using hRg (subset_tsupport _ h1) :
        ‖horizontal x‖ ≤ Rg).trans (le_max_right _ _)
    have hn2 : |x (Fin.last m)| ≤ Rψ := by
      simpa [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hRψ (subset_tsupport ψ h2)
    have hsq : ‖x‖ ^ 2 ≤ max Rφ Rg ^ 2 + Rψ ^ 2 := by
      rw [norm_sq_eq_horizontal_add_last_sq]
      have hs1 : ‖horizontal x‖ ^ 2 ≤ max Rφ Rg ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn1 2
      have hs2 : x (Fin.last m) ^ 2 ≤ Rψ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hn2 2
      linarith
    rw [mem_closedBall, dist_zero_right]
    linarith [Real.le_sqrt_of_sq_le hsq]
  obtain ⟨Cg, hCg⟩ := gradient_bound_of_locallyLipschitz hv_lip hK
  have hvt_le (x : Space (m + 1)) (hx : x ∈ K) : |verticalDerivative v x| ≤ Cg := by
    rw [← Real.norm_eq_abs, ← inner_gradient_verticalDirection]
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (by rw [norm_verticalDirection, mul_one]; exact hCg x hx)
  have hhg_le (x : Space (m + 1)) (hx : x ∈ K) : ‖horizontal (gradient v x)‖ ≤ Cg := by
    have hsq := norm_sq_eq_horizontal_add_last_sq (gradient v x)
    have hle : ‖horizontal (gradient v x)‖ ^ 2 ≤ ‖gradient v x‖ ^ 2 := by
      linarith [sq_nonneg (gradient v x (Fin.last m))]
    exact (nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
      (by simpa only [sq] using hle)).trans (hCg x hx)
  have hm_vt : Measurable (verticalDerivative v) := measurable_verticalDerivative v
  have hm_hg : Measurable (fun x : Space (m + 1) ↦ horizontal (gradient v x)) :=
    continuous_horizontal.measurable.comp (measurable_gradient v)
  have hi_vt_K : IntegrableOn (fun x ↦ R⁻¹ * verticalDerivative v x ^ 2) K := by
    apply (continuousOn_const.integrableOn_compact hK
      (f := fun _ ↦ R⁻¹ * (Cg : ℝ) ^ 2)).mono'
      (measurable_const.mul (hm_vt.pow_const 2)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), norm_pow, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hvt_le x hx) 2)
      (inv_nonneg.mpr hR.le)
  have hi_A_K : IntegrableOn
      (fun x ↦ rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) K :=
    (hiE K hK).sub hi_vt_K
  have hiI : Integrable (fun x : Space (m + 1) ↦
      (φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) :=
    integrable_mul_continuous_of_tsupport_subset hK
      (((hφ.continuous.comp continuous_horizontal).pow 2).mul
        ((hψ.continuous.comp continuous_last).pow 2)) hi_A_K
      (fun x hx ↦ by
        by_cases h1 : φ (horizontal x) = 0
        · simp [h1]
        · have h2 : ψ (x (Fin.last m)) = 0 := by
            by_contra h2; exact hx (hmem_K_of_φψ h1 h2)
          simp [h2])
  have hc_gphi : Continuous (fun x : Space (m + 1) ↦ gradient φ (horizontal x)) :=
    hgradφ_cont.comp continuous_horizontal
  obtain ⟨Mgφ, hMgφ⟩ := hK.exists_bound_of_continuousOn hc_gphi.continuousOn
  have hi_back : IntegrableOn (fun x : Space (m + 1) ↦
      verticalDerivative v x *
        inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x))) K := by
    apply (continuousOn_const.integrableOn_compact hK
      (f := fun _ ↦ (Cg : ℝ) * ((Cg : ℝ) * |Mgφ|))).mono'
      (hm_vt.mul (hm_hg.inner (𝕜 := ℝ) hc_gphi.measurable)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have hin : ‖inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x))‖ ≤
        (Cg : ℝ) * |Mgφ| :=
      (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (hhg_le x hx) ((hMgφ x hx).trans (le_abs_self Mgφ))
          (norm_nonneg _) Cg.coe_nonneg)
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs (verticalDerivative v x)]
    exact mul_le_mul (hvt_le x hx) hin (norm_nonneg _) Cg.coe_nonneg
  have hc_dt : Continuous (fun x : Space (m + 1) ↦ x (Fin.last m) - lam) :=
    (continuous_last (m := m)).sub continuous_const
  have hi_cross : Integrable (fun x : Space (m + 1) ↦
      2 * (φ (horizontal x) * ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) *
        R⁻¹ * verticalDerivative v x *
          inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x)))) := by
    have hc_front : Continuous (fun x : Space (m + 1) ↦
        2 * (φ (horizontal x) * ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) * R⁻¹)) :=
      continuous_const.mul (((((hφ.continuous.comp continuous_horizontal).mul
        ((hψ.continuous.comp (continuous_last (m := m))).pow 2)).mul hc_dt).mul continuous_const))
    have hi0 := integrable_mul_continuous_of_tsupport_subset hK hc_front hi_back
      (fun x hx ↦ by
        by_cases h1 : φ (horizontal x) = 0
        · simp [h1]
        · have h2 : ψ (x (Fin.last m)) = 0 := by
            by_contra h2; exact hx (hmem_K_of_φψ h1 h2)
          simp [h2])
    exact hi0.congr (Eventually.of_forall fun x ↦ by dsimp only; ring)
  have hi_gradφ : Integrable (fun x : Space (m + 1) ↦
      ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) ^ 2 *
        R⁻¹ * verticalDerivative v x ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2) := by
    have hc_fac : Continuous (fun x : Space (m + 1) ↦
        ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2) :=
      (((hψ.continuous.comp (continuous_last (m := m))).pow 2).mul
        (hc_dt.pow 2)).mul (hc_gphi.norm.pow 2)
    have hi0 := integrable_mul_continuous_of_tsupport_subset hK hc_fac hi_vt_K
      (fun x hx ↦ by
        by_cases h1 : gradient φ (horizontal x) = 0
        · simp [h1]
        · have h2 : ψ (x (Fin.last m)) = 0 := by
            by_contra h2; exact hx (hmem_K_of_gφψ h1 h2)
          simp [h2])
    exact hi0.congr (Eventually.of_forall fun x ↦ by dsimp only; ring)
  have hψ' : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hi_err_A : Integrable (fun x : Space (m + 1) ↦
      (φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
        (x (Fin.last m) - lam)) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) := by
    have hc_fac : Continuous (fun x : Space (m + 1) ↦
        φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
          (x (Fin.last m) - lam)) :=
      ((((hφ.continuous.comp continuous_horizontal).pow 2).mul
        (hψ.continuous.comp (continuous_last (m := m)))).mul
        (hψ'.comp (continuous_last (m := m)))).mul hc_dt
    exact integrable_mul_continuous_of_tsupport_subset hK hc_fac hi_A_K
      (fun x hx ↦ by
        by_cases h1 : φ (horizontal x) = 0
        · simp [h1]
        · have h2 : ψ (x (Fin.last m)) = 0 := by
            by_contra h2; exact hx (hmem_K_of_φψ h1 h2)
          simp [h2])
  have hi_err_E : Integrable (fun x : Space (m + 1) ↦
      (φ (horizontal x) ^ 2 *
        |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - lam)|) *
        rescaledPhaseEnergyDensity f R v x) := by
    have hc_fac : Continuous (fun x : Space (m + 1) ↦
        φ (horizontal x) ^ 2 *
          |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - lam)|) :=
      ((hφ.continuous.comp continuous_horizontal).pow 2).mul
        ((((hψ.continuous.comp (continuous_last (m := m))).mul
          (hψ'.comp (continuous_last (m := m)))).mul hc_dt).abs)
    exact integrable_mul_continuous_of_tsupport_subset hK hc_fac (hiE K hK)
      (fun x hx ↦ by
        by_cases h1 : φ (horizontal x) = 0
        · simp [h1]
        · have h2 : ψ (x (Fin.last m)) = 0 := by
            by_contra h2; exact hx (hmem_K_of_φψ h1 h2)
          simp [h2])
  have hi_rhs_young : Integrable (fun x : Space (m + 1) ↦
      (1 / 2) * (φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) +
      2 * (ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) ^ 2 *
        R⁻¹ * verticalDerivative v x ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2)) :=
    (hiI.const_mul (1 / 2)).add (hi_gradφ.const_mul 2)
  have hyoung : 2 * (∫ x, φ (horizontal x) * ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) *
      R⁻¹ * verticalDerivative v x *
        inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x))) ≤
      (1 / 2) * (∫ x, φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) +
      2 * ∫ x, ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) ^ 2 *
        R⁻¹ * verticalDerivative v x ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2 := by
    have hmono : (∫ x, 2 * (φ (horizontal x) * ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) *
        R⁻¹ * verticalDerivative v x *
          inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x)))) ≤
        ∫ x, ((1 / 2) * (φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
          (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) +
          2 * (ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) ^ 2 *
            R⁻¹ * verticalDerivative v x ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2)) := by
      apply integral_mono hi_cross hi_rhs_young
      intro x
      exact height_caccioppoli_cross_pointwise (inv_nonneg.mpr hR.le)
        (by simpa only [Real.norm_eq_abs] using
          norm_inner_le_norm (𝕜 := ℝ) (horizontal (gradient v x)) (gradient φ (horizontal x)))
        (horizontal_gradient_sq_le_energy_sub_vertical_sq hR hv hmodica x)
    have hadd := integral_add (hiI.const_mul (1 / 2)) (hi_gradφ.const_mul 2)
    rw [integral_const_mul, hadd, integral_const_mul, integral_const_mul] at hmono
    exact hmono
  have herr : -(∫ x, φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
      (x (Fin.last m) - lam) *
      (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) ≤
      ∫ x, φ (horizontal x) ^ 2 *
        |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - lam)| *
        rescaledPhaseEnergyDensity f R v x := by
    have hmono : (∫ x, -((φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
        (x (Fin.last m) - lam)) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2))) ≤
        ∫ x, (φ (horizontal x) ^ 2 *
          |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - lam)|) *
          rescaledPhaseEnergyDensity f R v x := by
      apply integral_mono hi_err_A.neg hi_err_E
      intro x
      have hA0 := energy_sub_vertical_sq_nonneg hR hv hmodica x
      have hAe := energy_sub_vertical_sq_le_energy f hR v x
      calc
        -((φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
            (x (Fin.last m) - lam)) *
            (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) ≤
          |(φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
            (x (Fin.last m) - lam)) *
            (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)| :=
          neg_le_abs _
        _ = (φ (horizontal x) ^ 2 *
            |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - lam)|) *
            (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) := by
          have h1 : φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
              (x (Fin.last m) - lam) =
              φ (horizontal x) ^ 2 *
                (ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - lam)) := by ring
          rw [h1, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hA0]
        _ ≤ (φ (horizontal x) ^ 2 *
            |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - lam)|) *
            rescaledPhaseEnergyDensity f R v x :=
          mul_le_mul_of_nonneg_left hAe (mul_nonneg (sq_nonneg _) (abs_nonneg _))
    rwa [integral_neg] at hmono
  linarith

/-- One-phase localized horizontal-gradient Caccioppoli inequality (FE2.2). -/
theorem rescaled_height_caccioppoli {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    {v : Space (m + 1) → ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hv_lip : LocallyLipschitz v)
    (hmodica : ∀ x, (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 ≤ R * phasePotentialDensity f v x)
    (hiE : ∀ K : Set (Space (m + 1)), IsCompact K →
      IntegrableOn (rescaledPhaseEnergyDensity f R v) K)
    (hstress : ∀ X : Space (m + 1) → Space (m + 1), ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x, (rescaledPhaseEnergyDensity f R v x *
          fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) X x -
        R⁻¹ * inner ℝ (gradient v x) (fderiv ℝ X x (gradient v x)))) = 0)
    {φ : Space m → ℝ} {ψ : ℝ → ℝ} (lam : ℝ)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
        (R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2)) ≤
      4 * (∫ x, ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - lam) ^ 2 *
          R⁻¹ * verticalDerivative v x ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2) +
        4 * ∫ x, φ (horizontal x) ^ 2 *
          |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - lam)| *
          rescaledPhaseEnergyDensity f R v x := by
  apply le_trans _ (rescaled_height_excess_caccioppoli hR hv hv_lip hmodica hiE hstress lam
    hφ hcφ hψ hcψ)
  let K := tsupport (fun x : Space (m + 1) ↦ φ (horizontal x) * ψ (x (Fin.last m)))
  have hK : IsCompact K := hasCompactSupport_mul_horizontal_last hcφ hcψ
  obtain ⟨Cg, hCg⟩ := gradient_bound_of_locallyLipschitz hv_lip hK
  have hc1 : Continuous (fun x : Space (m + 1) ↦
      φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2) :=
    ((hφ.continuous.comp continuous_horizontal).pow 2).mul
      ((hψ.continuous.comp continuous_last).pow 2)
  have hm_vt : Measurable (verticalDerivative v) := measurable_verticalDerivative v
  have hm_hg : Measurable (fun x : Space (m + 1) ↦ horizontal (gradient v x)) :=
    continuous_horizontal.measurable.comp (measurable_gradient v)
  have hi_lhs : Integrable (fun x : Space (m + 1) ↦
      φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
        (R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2)) := by
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc1.continuousOn
    have hiK : IntegrableOn (fun x : Space (m + 1) ↦
        φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
          (R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2)) K := by
      apply (continuousOn_const.integrableOn_compact hK
        (f := fun _ ↦ |M| * (R⁻¹ * (Cg : ℝ) ^ 2))).mono'
        (hc1.measurable.mul (measurable_const.mul (hm_hg.norm.pow_const 2))).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      have hhg : ‖horizontal (gradient v x)‖ ^ 2 ≤ (Cg : ℝ) ^ 2 := by
        have hsq := norm_sq_eq_horizontal_add_last_sq (gradient v x)
        have hle : ‖horizontal (gradient v x)‖ ^ 2 ≤ ‖gradient v x‖ ^ 2 := by
          linarith [sq_nonneg (gradient v x (Fin.last m))]
        exact hle.trans (pow_le_pow_left₀ (norm_nonneg _) (hCg x hx) 2)
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hR.le) (sq_nonneg _))]
      exact mul_le_mul ((hM x hx).trans (le_abs_self M))
        (mul_le_mul_of_nonneg_left hhg (inv_nonneg.mpr hR.le))
        (mul_nonneg (inv_nonneg.mpr hR.le) (sq_nonneg _)) (abs_nonneg M)
    exact hiK.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      have hz : φ (horizontal x) * ψ (x (Fin.last m)) = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun z : Space (m + 1) ↦ φ (horizontal z) * ψ (z (Fin.last m))) hx
      rcases mul_eq_zero.mp hz with h0 | h0 <;> simp [h0])
  have hi_rhs : Integrable (fun x : Space (m + 1) ↦
      φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) := by
    have hi_vt : IntegrableOn (fun x ↦ R⁻¹ * verticalDerivative v x ^ 2) K := by
      apply (continuousOn_const.integrableOn_compact hK
        (f := fun _ ↦ R⁻¹ * (Cg : ℝ) ^ 2)).mono'
        (measurable_const.mul (hm_vt.pow_const 2)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      have hvt : |verticalDerivative v x| ≤ Cg := by
        rw [← Real.norm_eq_abs, ← inner_gradient_verticalDirection]
        exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (by rw [norm_verticalDirection, mul_one]; exact hCg x hx)
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), norm_pow, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hvt 2)
        (inv_nonneg.mpr hR.le)
    exact ((((hiE K hK).sub hi_vt).mul_continuousOn hc1.continuousOn hK).congr_fun
      (fun x _ ↦ by simp only [Pi.sub_apply]; ring) hK.measurableSet).integrable_of_forall_notMem_eq_zero
      (fun x hx ↦ by
        have hz : φ (horizontal x) * ψ (x (Fin.last m)) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun z : Space (m + 1) ↦ φ (horizontal z) * ψ (z (Fin.last m))) hx
        rcases mul_eq_zero.mp hz with h0 | h0 <;> simp [h0])
  apply integral_mono hi_lhs hi_rhs
  intro x
  exact mul_le_mul_of_nonneg_left (horizontal_gradient_sq_le_energy_sub_vertical_sq hR hv hmodica x)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-! ### Second-order potential coercivity, `cosh` cube barrier and exponential tails (FE3) -/

/-- Two-sided second-order reaction and potential bounds in a neighborhood `[1 - b, 1]` of the
stable equilibrium, requiring only `C¹` regularity of `f` (`C²` regularity of `W`). -/
theorem RigidityHypotheses.exists_stable_well_potential_bounds
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ b c C : ℝ, b ∈ Ioo 0 1 ∧ 0 < c ∧ c ≤ C ∧
      ∀ s ∈ Icc (1 - b) 1,
        c * (1 - s) ≤ f s ∧ f s ≤ C * (1 - s) ∧
        (c / 2) * (1 - s) ^ 2 ≤ normalizedPotential f s ∧
        normalizedPotential f s ≤ (C / 2) * (1 - s) ^ 2 := by
  obtain ⟨c, δ, hc, hδ, hb_deriv⟩ := hr.exists_reaction_deriv_bound h
  let b : ℝ := min (δ / 2) (1 / 2)
  have hb : b ∈ Ioo (0 : ℝ) 1 := by
    have hmin := lt_min (half_pos hδ) (by norm_num : (0 : ℝ) < 1 / 2)
    have hle := min_le_right (δ / 2) (1 / 2)
    dsimp only [b]
    constructor <;> linarith
  have hsub_pos : Icc (1 - b) 1 ⊆ Ioi (0 : ℝ) := by
    intro s hs
    have hle : b ≤ 1 / 2 := min_le_right _ _
    simp only [mem_Ioi]
    linarith [hs.1]
  have hdf_cont : ContinuousOn (deriv f) (Icc (1 - b) 1) :=
    ((h.reaction_contDiffOn.mono Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by simp)).mono hsub_pos
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hdf_cont
  let C : ℝ := max c |M|
  have hcC : c ≤ C := le_max_left _ _
  have hderiv_bounds : ∀ t ∈ Icc (1 - b) 1, c ≤ -deriv f t ∧ -deriv f t ≤ C := by
    intro t ht
    have htd : |t - 1| < δ := by
      rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
      have hle : b ≤ δ / 2 := min_le_left _ _
      linarith [ht.1]
    refine ⟨(hb_deriv t htd).2, ?_⟩
    have hm := (hM t ht).trans (le_abs_self M)
    rw [Real.norm_eq_abs] at hm
    exact (neg_le_abs _).trans (hm.trans (le_max_right _ _))
  have hf_bounds : ∀ s ∈ Icc (1 - b) 1, c * (1 - s) ≤ f s ∧ f s ≤ C * (1 - s) := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hslt | rfl
    · have hspos : 0 < s := hsub_pos hs
      have hcont : ContinuousOn f (Icc s 1) :=
        h.reaction_contDiffOn.continuousOn.mono (fun t ht ↦ hspos.le.trans ht.1)
      have hdiff : DifferentiableOn ℝ f (Ioo s 1) := by
        intro t ht
        exact ((h.reaction_contDiffOn.differentiableOn_one t
          (hspos.le.trans ht.1.le)).differentiableAt
          (Ici_mem_nhds (hspos.trans ht.1))).differentiableWithinAt
      obtain ⟨t, ht, heq⟩ := exists_deriv_eq_slope f hslt hcont hdiff
      have ht_mem : t ∈ Icc (1 - b) 1 := ⟨hs.1.trans ht.1.le, ht.2.le⟩
      obtain ⟨hlo, hhi⟩ := hderiv_bounds t ht_mem
      have hslope : f 1 - f s = deriv f t * (1 - s) := by
        have h1 := (eq_div_iff (sub_pos.mpr hslt).ne').mp heq
        linarith
      rw [hr.reaction_one, zero_sub] at hslope
      have hpos : 0 ≤ 1 - s := sub_nonneg.mpr hslt.le
      constructor
      · have hm := mul_le_mul_of_nonneg_right hlo hpos
        linarith
      · have hm := mul_le_mul_of_nonneg_right hhi hpos
        linarith
    · simp [hr.reaction_one]
  refine ⟨b, c, C, hb, hc, hcC, ?_⟩
  intro s hs
  obtain ⟨hflo, hfhi⟩ := hf_bounds s hs
  refine ⟨hflo, hfhi, ?_, ?_⟩
  · let H : ℝ → ℝ := fun t ↦ (c / 2) * (1 - t) ^ 2 - normalizedPotential f t
    have hdH : ∀ t ∈ Icc s 1, HasDerivAt H (f t - c * (1 - t)) t := by
      intro t ht
      have htpos : 0 < t := hsub_pos ⟨hs.1.trans ht.1, ht.2⟩
      have hd1 : HasDerivAt (fun r ↦ (c / 2) * (1 - r) ^ 2) (-c * (1 - t)) t := by
        have hs1 : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) t := by
          convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) using 1
          · ext r; rfl
          · ring
        convert (hs1.pow 2).const_mul (c / 2) using 1
        ring
      convert hd1.sub (h.normalizedPotential_hasDerivAt htpos) using 1
      ring
    have hmono : MonotoneOn H (Icc s 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc s 1)
      · exact fun t ht ↦ (hdH t ht).continuousAt.continuousWithinAt
      · exact fun t ht ↦ (hdH t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht_cc : t ∈ Icc s 1 := interior_subset ht
        rw [(hdH t ht_cc).deriv]
        linarith [(hf_bounds t ⟨hs.1.trans ht_cc.1, ht_cc.2⟩).1]
    have hle := hmono ⟨le_rfl, hs.2⟩ ⟨hs.2, le_rfl⟩ hs.2
    dsimp only [H] at hle
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      normalizedPotential_one] at hle
    linarith
  · let G : ℝ → ℝ := fun t ↦ normalizedPotential f t - (C / 2) * (1 - t) ^ 2
    have hdG : ∀ t ∈ Icc s 1, HasDerivAt G (C * (1 - t) - f t) t := by
      intro t ht
      have htpos : 0 < t := hsub_pos ⟨hs.1.trans ht.1, ht.2⟩
      have hd1 : HasDerivAt (fun r ↦ (C / 2) * (1 - r) ^ 2) (-C * (1 - t)) t := by
        have hs1 : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) t := by
          convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) using 1
          · ext r; rfl
          · ring
        convert (hs1.pow 2).const_mul (C / 2) using 1
        ring
      convert (h.normalizedPotential_hasDerivAt htpos).sub hd1 using 1
      ring
    have hmono : MonotoneOn G (Icc s 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc s 1)
      · exact fun t ht ↦ (hdG t ht).continuousAt.continuousWithinAt
      · exact fun t ht ↦ (hdG t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht_cc : t ∈ Icc s 1 := interior_subset ht
        rw [(hdG t ht_cc).deriv]
        linarith [(hf_bounds t ⟨hs.1.trans ht_cc.1, ht_cc.2⟩).2]
    have hle := hmono ⟨le_rfl, hs.2⟩ ⟨hs.2, le_rfl⟩ hs.2
    dsimp only [G] at hle
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      normalizedPotential_one] at hle
    linarith

/-- Open coordinate cube `{x : Space d | ∀ i, |(x - x₀) i| < L}`. -/
def openCoordCube {d : ℕ} (x₀ : Space d) (L : ℝ) : Set (Space d) :=
  {x | ∀ i : Fin d, |(x - x₀) i| < L}

/-- Closed coordinate cube `{x : Space d | ∀ i, |(x - x₀) i| ≤ L}`. -/
def closedCoordCube {d : ℕ} (x₀ : Space d) (L : ℝ) : Set (Space d) :=
  {x | ∀ i : Fin d, |(x - x₀) i| ≤ L}

theorem isOpen_openCoordCube {d : ℕ} (x₀ : Space d) (L : ℝ) :
    IsOpen (openCoordCube x₀ L) := by
  have heq : openCoordCube x₀ L = ⋂ i : Fin d, {x : Space d | |(x - x₀) i| < L} := by
    ext x; simp [openCoordCube]
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_lt (((EuclideanSpace.proj i).continuous.comp
      (continuous_id.sub continuous_const)).abs) continuous_const

theorem isClosed_closedCoordCube {d : ℕ} (x₀ : Space d) (L : ℝ) :
    IsClosed (closedCoordCube x₀ L) := by
  have heq : closedCoordCube x₀ L = ⋂ i : Fin d, {x : Space d | |(x - x₀) i| ≤ L} := by
    ext x; simp [closedCoordCube]
  rw [heq]
  exact isClosed_iInter fun i ↦
    isClosed_le (((EuclideanSpace.proj i).continuous.comp
      (continuous_id.sub continuous_const)).abs) continuous_const

theorem openCoordCube_subset_closedCoordCube {d : ℕ} (x₀ : Space d) (L : ℝ) :
    openCoordCube x₀ L ⊆ closedCoordCube x₀ L :=
  fun _ hx i ↦ (hx i).le

theorem closure_openCoordCube_subset_closedCoordCube {d : ℕ} (x₀ : Space d) (L : ℝ) :
    closure (openCoordCube x₀ L) ⊆ closedCoordCube x₀ L :=
  closure_minimal (openCoordCube_subset_closedCoordCube x₀ L) (isClosed_closedCoordCube x₀ L)

/-- Explicit hyperbolic cosine cube supersolution barrier `B(x) = b * ∑_i cosh(k x_i) / cosh(k L)`
centered at the origin. -/
def coshCubeBarrier {d : ℕ} (b k L : ℝ) (x : Space d) : ℝ :=
  (b / Real.cosh (k * L)) * ∑ i : Fin d, Real.cosh (k * x i)

theorem contDiff_coshCubeBarrier {d : ℕ} (b k L : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (coshCubeBarrier (d := d) b k L) :=
  contDiff_const.mul (ContDiff.sum fun i _ ↦
    Real.contDiff_cosh.comp
      (contDiff_const.mul (EuclideanSpace.proj i : Space d →L[ℝ] ℝ).contDiff))

/-- Exact eigenfunction identity `Δ B = k² B` for `coshCubeBarrier`. -/
theorem laplacian_coshCubeBarrier {d : ℕ} (b k L : ℝ) (x : Space d) :
    (Δ (coshCubeBarrier b k L)) x = k ^ 2 * coshCubeBarrier b k L x := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  let A : ℝ := b / Real.cosh (k * L)
  have hd := ((contDiff_coshCubeBarrier (d := d) b k L (n := 2)).fderiv_right
    (by norm_num)).differentiable_one x
  rw [laplacian_eq_sum_fderiv e hd]
  have hfirst (j : Fin d) (y : Space d) :
      fderiv ℝ (coshCubeBarrier b k L) y (e j) = A * (k * Real.sinh (k * y j)) := by
    have hsum : HasFDerivAt (fun z : Space d ↦ ∑ i : Fin d, Real.cosh (k * z i))
        (∑ i : Fin d, Real.sinh (k * y i) • k •
          (EuclideanSpace.proj i : Space d →L[ℝ] ℝ)) y := by
      have hi (i : Fin d) : HasFDerivAt (fun z : Space d ↦ Real.cosh (k * z i))
          (Real.sinh (k * y i) • k • (EuclideanSpace.proj i : Space d →L[ℝ] ℝ)) y := by
        have h1 : HasFDerivAt (fun z : Space d ↦ k * z i)
            (k • (EuclideanSpace.proj i : Space d →L[ℝ] ℝ)) y :=
          (EuclideanSpace.proj i : Space d →L[ℝ] ℝ).hasFDerivAt.const_mul k
        exact (Real.hasDerivAt_cosh (k * y i)).comp_hasFDerivAt y h1
      convert HasFDerivAt.sum (u := Finset.univ) (fun i _ ↦ hi i) using 1
      ext z; simp
    have hbar : HasFDerivAt (coshCubeBarrier b k L)
        (A • ∑ i : Fin d, Real.sinh (k * y i) • k •
          (EuclideanSpace.proj i : Space d →L[ℝ] ℝ)) y := hsum.const_mul A
    rw [hbar.fderiv]
    simp only [smul_apply, sum_apply, PiLp.proj_apply, smul_eq_mul]
    have hterm (i : Fin d) : Real.sinh (k * y i) * (k * (e j) i) =
        if i = j then k * Real.sinh (k * y j) else 0 := by
      have hej : (e j) i = if i = j then 1 else 0 := by
        simp [e, EuclideanSpace.basisFun_apply, PiLp.single_apply]
      rw [hej]
      split_ifs with hij
      · subst hij; ring
      · ring
    simp_rw [hterm]
    rw [Finset.sum_ite_eq' Finset.univ j]
    simp only [Finset.mem_univ, ↓reduceIte]
  have hsecond (j : Fin d) :
      fderiv ℝ (fun y ↦ fderiv ℝ (coshCubeBarrier b k L) y (e j)) x (e j) =
        A * (k ^ 2 * Real.cosh (k * x j)) := by
    simp_rw [hfirst j]
    have hj1 : HasFDerivAt (fun y : Space d ↦ k * y j)
        (k • (EuclideanSpace.proj j : Space d →L[ℝ] ℝ)) x :=
      (EuclideanSpace.proj j : Space d →L[ℝ] ℝ).hasFDerivAt.const_mul k
    have hj2 : HasFDerivAt (fun y : Space d ↦ A * (k * Real.sinh (k * y j)))
        ((A * k) • ((Real.cosh (k * x j)) •
          (k • (EuclideanSpace.proj j : Space d →L[ℝ] ℝ)))) x := by
      have hs := ((Real.hasDerivAt_sinh (k * x j)).comp_hasFDerivAt x hj1).const_mul (A * k)
      convert hs using 1
      ext y; dsimp only [Function.comp_apply]; ring
    rw [hj2.fderiv]
    simp only [smul_apply, PiLp.proj_apply, smul_eq_mul]
    have hejj : (e j) j = 1 := by simp [e, EuclideanSpace.basisFun_apply]
    rw [hejj]
    ring
  simp_rw [hsecond]
  dsimp only [coshCubeBarrier, A]
  simp_rw [← Finset.mul_sum]
  ring

/-- Elementary hyperbolic cosine ratio bound on subcubes `|s| ≤ L - d_margin`. -/
theorem cosh_div_cosh_le_two_mul_exp_neg {k L d_margin s : ℝ}
    (hk : 0 ≤ k) (_hd : 0 ≤ d_margin) (_hdL : d_margin ≤ L) (hs : |s| ≤ L - d_margin) :
    Real.cosh (k * s) / Real.cosh (k * L) ≤ 2 * Real.exp (-k * d_margin) := by
  have habs : Real.cosh (k * s) = Real.cosh (k * |s|) := by
    rcases le_total 0 s with hs0 | hs0
    · rw [abs_of_nonneg hs0]
    · rw [abs_of_nonpos hs0, mul_neg, Real.cosh_neg]
  rw [habs]
  let a := k * |s|
  let M := k * L
  have ha0 : 0 ≤ a := mul_nonneg hk (abs_nonneg s)
  have ha_le : a ≤ M - k * d_margin := by
    have hm := mul_le_mul_of_nonneg_left hs hk
    dsimp only [a, M]
    linarith
  have hnum : Real.cosh a ≤ Real.exp M * Real.exp (-k * d_margin) := by
    rw [Real.cosh_eq, ← Real.exp_add]
    have hexp_neg : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
    have hexp_le : Real.exp a ≤ Real.exp (M + -k * d_margin) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hden : Real.exp M / 2 ≤ Real.cosh M := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-M)]
  have hden_pos : 0 < Real.exp M / 2 := half_pos (Real.exp_pos M)
  calc
    Real.cosh a / Real.cosh M ≤ (Real.exp M * Real.exp (-k * d_margin)) / (Real.exp M / 2) :=
      div_le_div₀ (mul_nonneg (Real.exp_pos M).le (Real.exp_pos _).le) hnum hden_pos hden
    _ = 2 * Real.exp (-k * d_margin) := by
      have hne : Real.exp M ≠ 0 := (Real.exp_pos M).ne'
      field_simp

/-- Quantitative exponential phase and energy tails near the stable equilibrium (FE3.1 and FE3.2):
if a rotated/translated rescaling `v x := zeroExtension g u (c₀ + R • Q x)` stays in `[1 - b, 1]`
throughout `closedCoordCube x₀ L`, then on every strict interior subcube
`closedCoordCube x₀ (L - d_margin)` (`0 < d_margin ≤ L`) both `1 - v` and `e_R` decay
exponentially in `R`. -/
theorem RigidityHypotheses.rescaled_stable_well_exponential_tail
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {b c C : ℝ} (hb : b ∈ Ioo 0 1) (hc : 0 < c)
    (hf_lo : ∀ s ∈ Icc (1 - b) 1, c * (1 - s) ≤ f s)
    (hW_hi : ∀ s ∈ Icc (1 - b) 1, normalizedPotential f s ≤ (C / 2) * (1 - s) ^ 2)
    (c₀ : Space (m + 1)) {R : ℝ} (hR : 0 < R)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (x₀ : Space (m + 1)) {L d_margin : ℝ} (hd_pos : 0 < d_margin) (hdL : d_margin ≤ L)
    (hwell : ∀ x ∈ closedCoordCube x₀ L,
      1 - b ≤ zeroExtension g u (c₀ + R • Q x)) :
    ∀ x ∈ closedCoordCube x₀ (L - d_margin),
      0 ≤ 1 - zeroExtension g u (c₀ + R • Q x) ∧
      1 - zeroExtension g u (c₀ + R • Q x) ≤
        2 * (m + 1 : ℝ) * b * Real.exp (-Real.sqrt c * d_margin * R) ∧
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c₀ + R • Q y)) x ≤
        4 * C * (m + 1 : ℝ) ^ 2 * b ^ 2 * R * Real.exp (-2 * Real.sqrt c * d_margin * R) := by
  have hL : 0 < L := hd_pos.trans_le hdL
  let c₁ : Space (m + 1) := c₀ + R • Q x₀
  let v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (c₁ + R • Q z)
  have hv_shift (z : Space (m + 1)) :
      v z = zeroExtension g u (c₀ + R • Q (z + x₀)) := by
    dsimp only [v, c₁]
    rw [map_add, smul_add, add_comm (R • Q z) (R • Q x₀), add_assoc]
  have hv_well : ∀ z ∈ closedCoordCube (0 : Space (m + 1)) L, 1 - b ≤ v z := by
    intro z hz
    rw [hv_shift]
    apply hwell (z + x₀)
    intro i
    simpa only [add_sub_cancel_right, sub_zero] using hz i
  let Ω := openCoordCube (0 : Space (m + 1)) L
  have hΩ : IsOpen Ω := isOpen_openCoordCube 0 L
  let k : ℝ := Real.sqrt c * R
  have hk : 0 < k := mul_pos (Real.sqrt_pos.mpr hc) hR
  have hk_sq : k ^ 2 = c * R ^ 2 := by
    dsimp only [k]
    rw [mul_pow, Real.sq_sqrt hc.le]
  let B := coshCubeBarrier (d := m + 1) b k L
  let w : Space (m + 1) → ℝ := fun z ↦ 1 - v z
  let q : Space (m + 1) → ℝ := fun z ↦ w z - B z
  have hmem_epi (z : Space (m + 1)) (hz : z ∈ closedCoordCube 0 L) :
      c₁ + R • Q z ∈ epigraph g := by
    have hpos : 0 < v z := by linarith [hb.2, hv_well z hz]
    exact (h.zeroExtension_pos_iff _).mp hpos
  let U_pos : Set (Space (m + 1)) := {z | c₁ + R • Q z ∈ epigraph g}
  have hU_open : IsOpen U_pos :=
    (isOpen_epigraph h.graph_contDiff.continuous).preimage
      (continuous_const.add ((Q.continuous).const_smul R))
  have hv_C2 : ContDiffOn ℝ 2 v U_pos := by
    have hu_comp : ContDiffOn ℝ 2 (fun z ↦ u (c₁ + R • Q z)) U_pos :=
      h.solution_contDiffOn.comp (contDiff_const.add (Q.contDiff.const_smul R)).contDiffOn
        (fun z hz ↦ hz)
    exact hu_comp.congr (fun z hz ↦ zeroExtension_of_mem hz)
  have hΩ_sub : Ω ⊆ U_pos :=
    fun z hz ↦ hmem_epi z (openCoordCube_subset_closedCoordCube 0 L hz)
  have hq_C2 : ContDiffOn ℝ 2 q Ω :=
    (contDiffOn_const.sub (hv_C2.mono hΩ_sub)).sub
      (contDiff_coshCubeBarrier (d := m + 1) b k L).contDiffOn
  have hv_cont : Continuous v :=
    h.zeroExtension_continuous.comp (continuous_const.add ((Q.continuous).const_smul R))
  have hq_cont : Continuous q :=
    (continuous_const.sub hv_cont).sub
      (contDiff_coshCubeBarrier (d := m + 1) b k L (n := 0)).continuous
  let F : Space (m + 1) → ℝ := fun z ↦ R ^ 2 * f (v z) - k ^ 2 * B z
  have hF_cont : Continuous F :=
    (continuous_const.mul (h.reaction_contDiffOn.continuousOn.comp_continuous hv_cont
      (fun z ↦ h.zeroExtension_nonneg _))).sub
      (continuous_const.mul (contDiff_coshCubeBarrier (d := m + 1) b k L (n := 0)).continuous)
  have heq_q : ∀ z ∈ Ω, (Δ q) z = F z := by
    intro z hz
    have hzU : z ∈ U_pos := hΩ_sub hz
    have hu_at : ContDiffAt ℝ 2 u (c₁ + R • Q z) :=
      h.solution_contDiffOn.contDiffAt ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hzU)
    have hU_at : ContDiffAt ℝ 2 (zeroExtension g u) (c₁ + R • Q z) :=
      hu_at.congr_of_eventuallyEq (zeroExtension_eventuallyEq h.graph_contDiff.continuous hzU)
    have hv_lap : (Δ v) z = -R ^ 2 * f (v z) := by
      have hlap := laplacian_comp_translate_dilation_isometry_of_contDiffAt c₁ R Q z hU_at
      have hloc := (laplacian_congr_nhds
        (zeroExtension_eventuallyEq (u := u) h.graph_contDiff.continuous hzU)).self_of_nhds
      have hpde := h.equation (c₁ + R • Q z) hzU
      dsimp only [v]
      rw [hlap, hloc, zeroExtension_of_mem hzU]
      linear_combination -R ^ 2 * hpde
    have hv_at : ContDiffAt ℝ 2 v z := hv_C2.contDiffAt (hU_open.mem_nhds hzU)
    have hw_at : ContDiffAt ℝ 2 w z := (contDiff_const.contDiffAt (x := z)).sub hv_at
    have hB_at : ContDiffAt ℝ 2 B z := (contDiff_coshCubeBarrier (d := m + 1) b k L).contDiffAt
    have hw_lap : (Δ w) z = R ^ 2 * f (v z) := by
      change (Δ ((fun _ : Space (m + 1) ↦ (1 : ℝ)) - v)) z = _
      rw [(contDiff_const.contDiffAt (x := z)).laplacian_sub hv_at]
      have h0 : (Δ (fun _ : Space (m + 1) ↦ (1 : ℝ))) z = 0 := by
        have hd0 : DifferentiableAt ℝ (fderiv ℝ fun _ : Space (m + 1) ↦ (1 : ℝ)) z :=
          ((contDiff_const (c := (1 : ℝ)) (n := (2 : ℕ∞ω))).fderiv_right
            (by norm_num)).differentiable_one z
        rw [laplacian_eq_sum_fderiv (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) hd0]
        simp [fderiv_const_apply]
      rw [h0, hv_lap]
      ring
    change (Δ (w - B)) z = F z
    rw [hw_at.laplacian_sub hB_at, hw_lap, laplacian_coshCubeBarrier]
  have hB_nonneg (z : Space (m + 1)) : 0 ≤ B z :=
    mul_nonneg (div_nonneg hb.1.le (Real.cosh_pos _).le)
      (Finset.sum_nonneg fun _ _ ↦ (Real.cosh_pos _).le)
  have hq_nonpos := nonpos_of_bounded_laplacian_ge_mul hΩ hq_C2 hq_cont.continuousOn
    hF_cont.continuousOn heq_q (mul_pos hc (sq_pos_of_pos hR))
    (M := 1) (fun z _ ↦ by
      dsimp only [q, w]
      linarith [h.zeroExtension_nonneg (c₁ + R • Q z), hB_nonneg z])
    (fun z hzcl hznot ↦ by
      have hz_cc : z ∈ closedCoordCube 0 L :=
        closure_openCoordCube_subset_closedCoordCube 0 L hzcl
      have hex : ∃ i : Fin (m + 1), |z i| = L := by
        by_contra hall
        push Not at hall
        apply hznot
        intro i
        have hle : |z i| ≤ L := by simpa only [sub_zero] using hz_cc i
        have hlt : |z i| < L := lt_of_le_of_ne hle (hall i)
        simpa only [sub_zero] using hlt
      obtain ⟨i₀, hi₀⟩ := hex
      have hsum_ge : Real.cosh (k * L) ≤ ∑ i : Fin (m + 1), Real.cosh (k * z i) := by
        have hterm : Real.cosh (k * z i₀) = Real.cosh (k * L) := by
          rcases le_total 0 (z i₀) with h0 | h0
          · rw [abs_of_nonneg h0] at hi₀; rw [hi₀]
          · rw [abs_of_nonpos h0] at hi₀
            have hneg : z i₀ = -L := by linarith
            rw [hneg, mul_neg, Real.cosh_neg]
        rw [← hterm]
        exact Finset.single_le_sum (f := fun i : Fin (m + 1) ↦ Real.cosh (k * z i))
          (fun i _ ↦ (Real.cosh_pos _).le) (Finset.mem_univ i₀)
      have hBz : b ≤ B z := by
        dsimp only [B, coshCubeBarrier]
        have h1 := mul_le_mul_of_nonneg_left hsum_ge (div_nonneg hb.1.le (Real.cosh_pos (k * L)).le)
        rwa [div_mul_cancel₀ _ (Real.cosh_pos (k * L)).ne'] at h1
      have hwz : w z ≤ b := by
        dsimp only [w]; linarith [hv_well z hz_cc]
      dsimp only [q]
      linarith)
    (fun z hz _ ↦ by
      have hz_cc := openCoordCube_subset_closedCoordCube 0 L hz
      have hvz_mem : v z ∈ Icc (1 - b) 1 :=
        ⟨hv_well z hz_cc, (hr.zeroExtension_lt_one _).le⟩
      have hfl := mul_le_mul_of_nonneg_left (hf_lo (v z) hvz_mem) (sq_nonneg R)
      dsimp only [F, q, w]
      rw [hk_sq]
      linarith)
  intro x hx
  let z : Space (m + 1) := x - x₀
  have hz_sub : z ∈ closedCoordCube 0 (L - d_margin) := by
    intro i; simpa only [z, sub_zero] using hx i
  have hz_open : z ∈ Ω := by
    intro i
    have hle : |z i| ≤ L - d_margin := by simpa only [sub_zero] using hz_sub i
    simp only [sub_zero]
    linarith
  have hw_le_B : 1 - v z ≤ B z := by
    have hq0 := hq_nonpos z (subset_closure hz_open)
    dsimp only [q, w] at hq0
    linarith
  have hB_bound : B z ≤ 2 * (m + 1 : ℝ) * b * Real.exp (-Real.sqrt c * d_margin * R) := by
    have hsum_le : (∑ i : Fin (m + 1), Real.cosh (k * z i) / Real.cosh (k * L)) ≤
        ∑ _i : Fin (m + 1), 2 * Real.exp (-k * d_margin) := by
      apply Finset.sum_le_sum
      intro i _
      exact cosh_div_cosh_le_two_mul_exp_neg hk.le hd_pos.le hdL
        (by simpa only [sub_zero] using hz_sub i)
    have hBz_eq : B z = b * ∑ i : Fin (m + 1), Real.cosh (k * z i) / Real.cosh (k * L) := by
      dsimp only [B, coshCubeBarrier]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [hBz_eq]
    have hmul := mul_le_mul_of_nonneg_left hsum_le hb.1.le
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one] at hmul
    have hexp_eq : -k * d_margin = -Real.sqrt c * d_margin * R := by dsimp only [k]; ring
    rw [hexp_eq] at hmul
    linarith
  have hv_zx : v z = zeroExtension g u (c₀ + R • Q x) := by
    rw [hv_shift]
    simp [z]
  have h1_nonneg : 0 ≤ 1 - zeroExtension g u (c₀ + R • Q x) :=
    sub_nonneg.mpr (hr.zeroExtension_lt_one _).le
  have h1_upper : 1 - zeroExtension g u (c₀ + R • Q x) ≤
      2 * (m + 1 : ℝ) * b * Real.exp (-Real.sqrt c * d_margin * R) := by
    rw [← hv_zx]
    exact hw_le_B.trans hB_bound
  refine ⟨h1_nonneg, h1_upper, ?_⟩
  have hmod_x := rescaledPhaseEnergyDensity_le_two_mul_potential
    (fun y ↦ h.zeroExtension_nonneg (c₀ + R • Q y))
    (hr.rescaled_isometry_modica_bound h c₀ hR Q) x
  have hx_L : x ∈ closedCoordCube x₀ L := fun i ↦ (hx i).trans (by linarith)
  have hvx_mem : zeroExtension g u (c₀ + R • Q x) ∈ Icc (1 - b) 1 :=
    ⟨hwell x hx_L, (hr.zeroExtension_lt_one _).le⟩
  have hvx_pos : 0 < zeroExtension g u (c₀ + R • Q x) := by linarith [hb.2, hvx_mem.1]
  have hpot_x : phasePotentialDensity f (fun y ↦ zeroExtension g u (c₀ + R • Q y)) x =
      normalizedPotential f (zeroExtension g u (c₀ + R • Q x)) := by
    simp [phasePotentialDensity, hvx_pos]
  have hW_x := hW_hi _ hvx_mem
  have hC0 : 0 ≤ C := by
    have h0 := hr.normalizedPotential_nonneg h ⟨le_trans (by linarith [hb.2]) hvx_mem.1, hvx_mem.2⟩
    have h1 : 0 ≤ (C / 2) * (1 - zeroExtension g u (c₀ + R • Q x)) ^ 2 := h0.trans hW_x
    by_cases h1v : 1 - zeroExtension g u (c₀ + R • Q x) = 0
    · have hs0 : 1 - b ∈ Icc (1 - b) 1 := ⟨le_rfl, by linarith [hb.1]⟩
      have h0' := hr.normalizedPotential_pos h (s := 1 - b) (by linarith [hb.2]) (by linarith [hb.1])
      have hW0 := hW_hi (1 - b) hs0
      have hb2 : 0 < (1 - (1 - b)) ^ 2 := by ring_nf; exact sq_pos_of_pos hb.1
      nlinarith
    · have hpos2 : 0 < (1 - zeroExtension g u (c₀ + R • Q x)) ^ 2 := sq_pos_of_ne_zero h1v
      nlinarith
  have hsq_le : (1 - zeroExtension g u (c₀ + R • Q x)) ^ 2 ≤
      4 * (m + 1 : ℝ) ^ 2 * b ^ 2 * Real.exp (-2 * Real.sqrt c * d_margin * R) := by
    have hpow := pow_le_pow_left₀ h1_nonneg h1_upper 2
    have hrhs_sq : (2 * (m + 1 : ℝ) * b * Real.exp (-Real.sqrt c * d_margin * R)) ^ 2 =
        4 * (m + 1 : ℝ) ^ 2 * b ^ 2 * Real.exp (-2 * Real.sqrt c * d_margin * R) := by
      rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]
      push_cast
      have hexp2 : (2 : ℝ) * (-Real.sqrt c * d_margin * R) = -2 * Real.sqrt c * d_margin * R := by
        ring
      rw [hexp2]
      ring
    rwa [hrhs_sq] at hpow
  calc
    rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c₀ + R • Q y)) x ≤
        2 * R * normalizedPotential f (zeroExtension g u (c₀ + R • Q x)) := by
      rwa [hpot_x] at hmod_x
    _ ≤ 2 * R * ((C / 2) * (1 - zeroExtension g u (c₀ + R • Q x)) ^ 2) :=
      mul_le_mul_of_nonneg_left hW_x (by positivity)
    _ = C * R * (1 - zeroExtension g u (c₀ + R • Q x)) ^ 2 := by ring
    _ ≤ C * R * (4 * (m + 1 : ℝ) ^ 2 * b ^ 2 * Real.exp (-2 * Real.sqrt c * d_margin * R)) :=
      mul_le_mul_of_nonneg_left hsq_le (mul_nonneg hC0 hR.le)
    _ = 4 * C * (m + 1 : ℝ) ^ 2 * b ^ 2 * R * Real.exp (-2 * Real.sqrt c * d_margin * R) := by
      ring

/-- Power-exponential decay as the rescaling parameter `R → ∞` (`R ^ p * exp (-a * R) → 0`
for any real exponent `p` and rate `a > 0`), used to eliminate cutoff errors after dividing by
powers of a tilt parameter `δ_j ≥ K * R_j⁻¹` (FE4.3). -/
theorem tendsto_rpow_mul_exp_neg_atTop_zero (p : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ ↦ R ^ p * Real.exp (-a * R)) atTop (𝓝 0) :=
  tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p a ha

/-- Natural-power specialization `R ^ k * exp (-a * R) → 0` as `R → ∞` for `a > 0`. -/
theorem tendsto_pow_mul_exp_neg_atTop_zero (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ ↦ R ^ k * Real.exp (-a * R)) atTop (𝓝 0) := by
  refine (tendsto_rpow_mul_exp_neg_atTop_zero (k : ℝ) ha).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [Real.rpow_natCast]

end SerrinEpigraph
