module

public import SerrinEpigraph.DiffuseTiltDecay

/-!
# HA6: strong weighted gradient convergence from the exact stress identity

This module formalizes HA6 of `docs/rigidity-proof/harmonic-approximation.md` in the vertical
frame. For a rescaled function `v` (scale `R`, `ε = R⁻¹`), a tilt scale `δ`, a center `a`, a `C²`
function `H` harmonic near the support of a horizontal cutoff `φ`, and a vertical cutoff `ψ`:

* the exact FE2 stress identity tested with `φ(y)² ψ(t)² (t - a) e_n`, used *without*
  Cauchy–Schwarz on its main term, bounds the normalized horizontal kinetic mass
  `∫ φ² ψ² ε |∇_y v|² / δ²` by twice the flux pairing `∫ ψ² ⟪φ H ∇φ, F⟫`
  (`F = ε ∂ₜ v ∇_y v / δ`), an error controlled by the height moment
  `∫ ψ² |∇φ|² ((t - a)/δ - H)² ε |∇v|²`, and the cutoff error `∫ φ² |ψ ψ' (t - a)| e / δ²`
  (`integral_ha6Square_le`);
* completing the square,
  `∫ φ² ψ² ε |∇_y v / δ + ∂ₜ v ∇H|² = ∫ φ² ψ² ε |∇_y v|²/δ² + 2 ∫ ψ² ⟪φ² ∇H, F⟫ + ∫ ψ² φ² |∇H|² ε (∂ₜ v)²`;
* along a sequence, if the height moment and the cutoff error tend to zero, the flux pairings
  converge to `-σ ∫ ⟪ζ, ∇H⟫` and the normal kinetic pairings are asymptotically at most `σ ∫ w`,
  then Green's identity `∫ φ² |∇H|² = -2 ∫ φ H ⟪∇H, ∇φ⟫` for the harmonic `H` forces the square
  to vanish in the limit (`tendsto_integral_ha6Square_of_limits`): the strong convergence of HA6;
* along HA11 contradiction sequences, the HA6 inputs `HasHarmonicHeightData` (weighted height
  approximation HA6.1, flux limit HA4, FE3 energy tails, normal kinetic bound) give the harmonic
  approximation interface `HasHarmonicApproximation` of `SerrinEpigraph.DiffuseTiltDecay`
  (`RigidityHypotheses.hasHarmonicApproximation_of_heightData`, with smooth bump cutoffs and the
  kinetic bound `2ᵐ` from the tilt normalization), hence the HA0 decay
  (`RigidityHypotheses.hasCylinderTiltDecay_of_heightData`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ}

/-! ## Integrability on compact supports -/

/-- A function dominated by `|c| P` with `c` continuous and compactly supported and `P`
integrable on the support of `c` is integrable. -/
theorem ha6_integrable_of_abs_le {d : ℕ} {G c P : Space d → ℝ} (hc : Continuous c)
    (hcc : HasCompactSupport c) (hP : IntegrableOn P (tsupport c))
    (hGm : AEStronglyMeasurable G (volume.restrict (tsupport c)))
    (hle : ∀ x, |G x| ≤ |c x| * P x) : Integrable G := by
  have hsupp : Function.support G ⊆ tsupport c := by
    intro x hx
    by_contra hxc
    have hc0 : c x = 0 := image_eq_zero_of_notMem_tsupport hxc
    have h1 := hle x
    rw [hc0, abs_zero, zero_mul] at h1
    exact hx (abs_nonpos_iff.mp h1)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  have hB : IntegrableOn (fun x ↦ |c x| * P x) (tsupport c) :=
    IntegrableOn.continuousOn_mul hc.abs.continuousOn hP hcc
  refine hB.mono' hGm ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact hle x

/-! ## Green's identity for harmonic functions -/

/-- A function vanishing wherever `φ` vanishes has topological support inside that of `φ`. -/
theorem ha6_tsupport_subset_of_zero {X : Type*} [TopologicalSpace X] {G φ : X → ℝ}
    (h : ∀ y, φ y = 0 → G y = 0) :
    tsupport G ⊆ tsupport φ :=
  closure_minimal (fun y hy ↦ subset_tsupport φ (fun h0 ↦ hy (h y h0))) (isClosed_tsupport φ)

/-- **Green's identity.** For `H` of class `C²` and harmonic on an open set containing the
support of a `C¹` cutoff `φ`: `∫ φ² |∇H|² = -2 ∫ φ H ⟪∇H, ∇φ⟫`. -/
theorem integral_sq_mul_norm_gradient_sq_of_harmonic {d : ℕ} {H φ : Space d → ℝ}
    {U : Set (Space d)} (hU : IsOpen U) (hH : ContDiff ℝ 2 H) (hΔ : ∀ y ∈ U, Δ H y = 0)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ y, φ y ^ 2 * ‖gradient H y‖ ^ 2) =
      -2 * ∫ y, φ y * H y * inner ℝ (gradient H y) (gradient φ y) := by
  set ψ : Space d → ℝ := fun y ↦ φ y * φ y * H y with hψdef
  have hψ : ContDiff ℝ 1 ψ := (hφ.mul hφ).mul (hH.of_le (by norm_num))
  have hψz : ∀ y, φ y = 0 → ψ y = 0 := fun y h0 ↦ by simp [hψdef, h0]
  have hψc : HasCompactSupport ψ :=
    hcφ.mono' ((subset_tsupport ψ).trans (ha6_tsupport_subset_of_zero hψz))
  have hψU : tsupport ψ ⊆ U := (ha6_tsupport_subset_of_zero hψz).trans hφU
  have hgreen := integral_inner_gradient_eq_neg_laplacian_mul (μ := volume) hU hH.contDiffOn hψ hψc
    hψU
  have hzero : (∫ x, (Δ H) x * ψ x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport ψ
    · rw [hΔ x (hψU hx), zero_mul]
      rfl
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
      rfl
  rw [hzero, neg_zero] at hgreen
  have hdφ (y : Space d) : DifferentiableAt ℝ φ y := hφ.differentiable one_ne_zero y
  have hdH (y : Space d) : DifferentiableAt ℝ H y := hH.differentiable (by norm_num) y
  have hpt (y : Space d) : inner ℝ (gradient H y) (gradient ψ y) =
      φ y ^ 2 * ‖gradient H y‖ ^ 2 +
        2 * (φ y * H y * inner ℝ (gradient H y) (gradient φ y)) := by
    have hd : HasFDerivAt ψ ((φ y * φ y) • fderiv ℝ H y +
        H y • (φ y • fderiv ℝ φ y + φ y • fderiv ℝ φ y)) y :=
      ((hdφ y).hasFDerivAt.mul (hdφ y).hasFDerivAt).mul (hdH y).hasFDerivAt
    rw [real_inner_comm, inner_gradient_left, hd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [← inner_gradient_left (f := H), ← inner_gradient_left (f := φ),
      real_inner_self_eq_norm_sq, real_inner_comm (gradient φ y)]
    ring
  simp_rw [hpt] at hgreen
  have hgH : Continuous (gradient H) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hH.continuous_fderiv (by norm_num))
  have hgφ : Continuous (gradient φ) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hi1 : Integrable (fun y ↦ φ y ^ 2 * ‖gradient H y‖ ^ 2) := by
    have hcont : Continuous (fun y ↦ φ y ^ 2 * ‖gradient H y‖ ^ 2) :=
      (hφ.continuous.pow 2).mul (hgH.norm.pow 2)
    exact hcont.integrable_of_hasCompactSupport
      (hcφ.mono' ((subset_tsupport _).trans (ha6_tsupport_subset_of_zero fun y h0 ↦ by simp [h0])))
  have hi2 : Integrable (fun y ↦ 2 * (φ y * H y * inner ℝ (gradient H y) (gradient φ y))) := by
    have hcont : Continuous (fun y ↦ 2 * (φ y * H y * inner ℝ (gradient H y) (gradient φ y))) :=
      continuous_const.mul ((hφ.continuous.mul hH.continuous).mul (hgH.inner hgφ))
    exact hcont.integrable_of_hasCompactSupport
      (hcφ.mono' ((subset_tsupport _).trans (ha6_tsupport_subset_of_zero fun y h0 ↦ by simp [h0])))
  rw [integral_add hi1 hi2, integral_const_mul] at hgreen
  linarith

/-- Integrability of a function dominated by a compactly supported product cutoff times a
function integrable on compact sets. -/
theorem ha6_integrable_of_abs_le_prod {G P : Space (m + 1) → ℝ} {α : Space m → ℝ} {β : ℝ → ℝ}
    (hα : Continuous α) (hcα : HasCompactSupport α) (hβ : Continuous β)
    (hcβ : HasCompactSupport β) (hP : ∀ K, IsCompact K → IntegrableOn P K)
    (hGm : ∀ K, IsCompact K → AEStronglyMeasurable G (volume.restrict K))
    (hle : ∀ x, |G x| ≤ |α (horizontal x) * β (x (Fin.last m))| * P x) : Integrable G := by
  have hc : Continuous (fun x : Space (m + 1) ↦ α (horizontal x) * β (x (Fin.last m))) :=
    (hα.comp continuous_horizontal).mul (hβ.comp continuous_last)
  have hcc := hasCompactSupport_mul_horizontal_last hcα hcβ
  exact ha6_integrable_of_abs_le hc hcc (hP _ hcc) (hGm _ hcc) hle

/-- Bound of a continuous function on the topological support of a compactly supported one. -/
theorem ha6_exists_bound_on_tsupport {d : ℕ} {φ : Space d → ℝ} (hcφ : HasCompactSupport φ)
    {F : Space d → ℝ} (hF : Continuous F) : ∃ M, 0 ≤ M ∧ ∀ y ∈ tsupport φ, |F y| ≤ M := by
  obtain ⟨M, hM⟩ := hcφ.isCompact.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y hy ↦ ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hM y hy).trans (le_max_left _ _)

theorem ha6_integrable_grad {v : Space (m + 1) → ℝ} (hvL : LocallyLipschitz v)
    {G : Space (m + 1) → ℝ} (hG : Measurable G) {α : Space m → ℝ} {β : ℝ → ℝ}
    (hα : Continuous α) (hcα : HasCompactSupport α) (hβ : Continuous β)
    (hcβ : HasCompactSupport β)
    (hle : ∀ x, |G x| ≤ |α (horizontal x) * β (x (Fin.last m))| * ‖gradient v x‖ ^ 2) :
    Integrable G :=
  ha6_integrable_of_abs_le_prod hα hcα hβ hcβ
    (fun _ hK ↦ integrableOn_gradient_sq_of_locallyLipschitz hvL hK)
    (fun _ _ ↦ hG.aestronglyMeasurable) hle

theorem ha6_hasCompactSupport_of_zero {X : Type*} [TopologicalSpace X] {φ α : X → ℝ}
    (hcφ : HasCompactSupport φ) (hα0 : ∀ y, φ y = 0 → α y = 0) : HasCompactSupport α :=
  hcφ.mono' ((subset_tsupport α).trans (ha6_tsupport_subset_of_zero hα0))

theorem ha6_abs_verticalDerivative_mul_le (v : Space (m + 1) → ℝ) (x : Space (m + 1)) :
    |verticalDerivative v x| * ‖horizontal (gradient v x)‖ ≤ ‖gradient v x‖ ^ 2 := by
  have h1 : |verticalDerivative v x| ≤ ‖gradient v x‖ :=
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
      (by rw [sq_abs]; exact verticalDerivative_sq_le_gradient v x)
  have h2 : ‖horizontal (gradient v x)‖ ≤ ‖gradient v x‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (horizontal_norm_sq_le_gradient v x)
  nlinarith [abs_nonneg (verticalDerivative v x), norm_nonneg (horizontal (gradient v x))]

theorem ha6_measurable_flux_vector (R δ : ℝ) (v : Space (m + 1) → ℝ) :
    Measurable (fun x : Space (m + 1) ↦
      ((δ⁻¹ * R⁻¹) * verticalDerivative v x) • horizontal (gradient v x)) :=
  (measurable_const.mul (measurable_verticalDerivative v)).smul
    (continuous_horizontal.measurable.comp (measurable_gradient v))

theorem ha6_abs_inner_flux_le {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (v : Space (m + 1) → ℝ)
    (w : Space m) (x : Space (m + 1)) :
    |inner ℝ w (((δ⁻¹ * R⁻¹) * verticalDerivative v x) • horizontal (gradient v x))| ≤
      ‖w‖ * (δ⁻¹ * R⁻¹) * ‖gradient v x‖ ^ 2 := by
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos (inv_pos.mpr hδ) (inv_pos.mpr hR))]
  have := ha6_abs_verticalDerivative_mul_le v x
  have h0 : 0 ≤ ‖w‖ * (δ⁻¹ * R⁻¹) := by positivity
  nlinarith [norm_nonneg w]

/-! ## The HA6 integrands -/

/-- The strong approximation integrand `φ² ψ² ε |∇_y v / δ + ∂ₜ v ∇H|²`. -/
def ha6Square (R δ : ℝ) (v : Space (m + 1) → ℝ) (H φ : Space m → ℝ) (ψ : ℝ → ℝ)
    (x : Space (m + 1)) : ℝ :=
  φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
    (R⁻¹ * ‖δ⁻¹ • horizontal (gradient v x) +
      verticalDerivative v x • gradient H (horizontal x)‖ ^ 2)

/-- The normalized horizontal kinetic integrand `φ² ψ² ε |∇_y v|² / δ²`. -/
def ha6Kin (R δ : ℝ) (v : Space (m + 1) → ℝ) (φ : Space m → ℝ) (ψ : ℝ → ℝ)
    (x : Space (m + 1)) : ℝ :=
  φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 * (R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2) / δ ^ 2

/-- The normalized flux pairing `ψ² ⟪ζ(y), ε ∂ₜ v ∇_y v / δ⟫`. -/
def ha6Flux (R δ : ℝ) (v : Space (m + 1) → ℝ) (ζ : Space m → Space m) (ψ : ℝ → ℝ)
    (x : Space (m + 1)) : ℝ :=
  ψ (x (Fin.last m)) ^ 2 * inner ℝ (ζ (horizontal x))
    (((δ⁻¹ * R⁻¹) * verticalDerivative v x) • horizontal (gradient v x))

/-- The normal kinetic pairing `ψ² w(y) ε (∂ₜ v)²`. -/
def ha6Normal (R : ℝ) (v : Space (m + 1) → ℝ) (w : Space m → ℝ) (ψ : ℝ → ℝ)
    (x : Space (m + 1)) : ℝ :=
  ψ (x (Fin.last m)) ^ 2 * w (horizontal x) * (R⁻¹ * verticalDerivative v x ^ 2)

/-- The height-moment integrand `ψ² |∇φ|² ((t - a)/δ - H(y))² ε |∇v|²`. -/
def ha6Height (R δ a : ℝ) (v : Space (m + 1) → ℝ) (H φ : Space m → ℝ) (ψ : ℝ → ℝ)
    (x : Space (m + 1)) : ℝ :=
  ψ (x (Fin.last m)) ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2 *
    ((x (Fin.last m) - a) / δ - H (horizontal x)) ^ 2 * (R⁻¹ * ‖gradient v x‖ ^ 2)

/-- The cutoff error integrand `φ² |ψ ψ' (t - a)| e / δ²`. -/
def ha6Tail (f : ℝ → ℝ) (R δ a : ℝ) (v : Space (m + 1) → ℝ) (φ : Space m → ℝ) (ψ : ℝ → ℝ)
    (x : Space (m + 1)) : ℝ :=
  φ (horizontal x) ^ 2 * |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - a)| *
    rescaledPhaseEnergyDensity f R v x / δ ^ 2

/-- The height error pairing `ψ² φ ((t - a)/δ - H) ⟪∇φ, F⟫`. -/
def ha6Err (R δ a : ℝ) (v : Space (m + 1) → ℝ) (H φ : Space m → ℝ) (ψ : ℝ → ℝ)
    (x : Space (m + 1)) : ℝ :=
  ψ (x (Fin.last m)) ^ 2 * (φ (horizontal x) * ((x (Fin.last m) - a) / δ - H (horizontal x))) *
    inner ℝ (gradient φ (horizontal x))
      (((δ⁻¹ * R⁻¹) * verticalDerivative v x) • horizontal (gradient v x))

/-! ## Pointwise identities -/

theorem ha6Square_eq {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (v : Space (m + 1) → ℝ)
    (H φ : Space m → ℝ) (ψ : ℝ → ℝ) (x : Space (m + 1)) :
    ha6Square R δ v H φ ψ x = ha6Kin R δ v φ ψ x +
      2 * ha6Flux R δ v (fun y ↦ φ y ^ 2 • gradient H y) ψ x +
        ha6Normal R v (fun y ↦ φ y ^ 2 * ‖gradient H y‖ ^ 2) ψ x := by
  unfold ha6Square ha6Kin ha6Flux ha6Normal
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_comm (gradient H (horizontal x)) (horizontal (gradient v x)),
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  have hR' : R ≠ 0 := hR.ne'
  have hδ' : δ ≠ 0 := hδ.ne'
  field_simp
  try ring

theorem ha6_kin_le {f : ℝ → ℝ} {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {v : Space (m + 1) → ℝ}
    (hv0 : ∀ x, 0 ≤ v x)
    (hmodica : ∀ x, (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 ≤ R * phasePotentialDensity f v x)
    (φ : Space m → ℝ) (ψ : ℝ → ℝ) (x : Space (m + 1)) :
    δ ^ 2 * ha6Kin R δ v φ ψ x ≤ φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
      (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) := by
  unfold ha6Kin
  rw [mul_div_cancel₀ _ (pow_ne_zero 2 hδ.ne')]
  exact mul_le_mul_of_nonneg_left
    (horizontal_gradient_sq_le_energy_sub_vertical_sq hR hv0 hmodica x) (by positivity)

theorem ha6_middle_eq {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (a : ℝ) (v : Space (m + 1) → ℝ)
    (H φ : Space m → ℝ) (ψ : ℝ → ℝ) (x : Space (m + 1)) :
    φ (horizontal x) * ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - a) * R⁻¹ *
        verticalDerivative v x * inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x)) =
      δ ^ 2 * (ha6Flux R δ v (fun y ↦ (φ y * H y) • gradient φ y) ψ x +
        ha6Err R δ a v H φ ψ x) := by
  unfold ha6Flux ha6Err
  rw [real_inner_smul_left, real_inner_smul_right,
    real_inner_comm (gradient φ (horizontal x)) (horizontal (gradient v x))]
  have hR' : R ≠ 0 := hR.ne'
  have hδ' : δ ≠ 0 := hδ.ne'
  field_simp
  try ring

theorem ha6_tail_le {f : ℝ → ℝ} {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (a : ℝ)
    {v : Space (m + 1) → ℝ} (hv0 : ∀ x, 0 ≤ v x)
    (hmodica : ∀ x, (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 ≤ R * phasePotentialDensity f v x)
    (φ : Space m → ℝ) (ψ : ℝ → ℝ) (x : Space (m + 1)) :
    |φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
        (x (Fin.last m) - a) * (rescaledPhaseEnergyDensity f R v x -
          R⁻¹ * verticalDerivative v x ^ 2)| ≤ δ ^ 2 * ha6Tail f R δ a v φ ψ x := by
  unfold ha6Tail
  rw [mul_div_cancel₀ _ (pow_ne_zero 2 hδ.ne')]
  have hEN := energy_sub_vertical_sq_nonneg hR hv0 hmodica x
  have hDE := energy_sub_vertical_sq_le_energy f hR v x
  have h1 : φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
      (x (Fin.last m) - a) * (rescaledPhaseEnergyDensity f R v x -
        R⁻¹ * verticalDerivative v x ^ 2) =
      φ (horizontal x) ^ 2 * (ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
        (x (Fin.last m) - a)) * (rescaledPhaseEnergyDensity f R v x -
          R⁻¹ * verticalDerivative v x ^ 2) := by ring
  rw [h1, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hEN]
  exact mul_le_mul_of_nonneg_left hDE (by positivity)

theorem ha6_err_le {R δ lam : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hlam : 0 < lam) (a : ℝ)
    (v : Space (m + 1) → ℝ) (H φ : Space m → ℝ) (ψ : ℝ → ℝ) (x : Space (m + 1)) :
    ha6Err R δ a v H φ ψ x ≤
      lam / 2 * ha6Height R δ a v H φ ψ x + 1 / (2 * lam) * ha6Kin R δ v φ ψ x := by
  unfold ha6Err ha6Height ha6Kin
  set y := horizontal x
  set t := x (Fin.last m)
  set hvx := horizontal (gradient v x)
  set vt := verticalDerivative v x
  set r := (t - a) / δ - H y
  set X : ℝ := |ψ t| * ‖gradient φ y‖ * |r| * |vt|
  set Y : ℝ := |ψ t| * |φ y| * ‖hvx‖ / δ
  have hcs := abs_real_inner_le_norm (gradient φ y) (((δ⁻¹ * R⁻¹) * vt) • hvx)
  rw [norm_smul, Real.norm_eq_abs] at hcs
  have h1 : ψ t ^ 2 * (φ y * r) * inner ℝ (gradient φ y) (((δ⁻¹ * R⁻¹) * vt) • hvx) ≤
      R⁻¹ * (X * Y) := by
    have hb : |ψ t ^ 2 * (φ y * r) * inner ℝ (gradient φ y) (((δ⁻¹ * R⁻¹) * vt) • hvx)| ≤
        R⁻¹ * (X * Y) := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow]
      calc |ψ t| ^ 2 * (|φ y| * |r|) *
            |inner ℝ (gradient φ y) (((δ⁻¹ * R⁻¹) * vt) • hvx)|
          ≤ |ψ t| ^ 2 * (|φ y| * |r|) * (‖gradient φ y‖ * (|δ⁻¹ * R⁻¹ * vt| * ‖hvx‖)) :=
            mul_le_mul_of_nonneg_left hcs (by positivity)
        _ = R⁻¹ * (X * Y) := by
            simp only [X, Y]
            rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hδ), abs_of_pos (inv_pos.mpr hR)]
            have hδ' : δ ≠ 0 := hδ.ne'
            field_simp
            try ring
    exact (le_abs_self _).trans hb
  have h2 : X * Y ≤ lam / 2 * X ^ 2 + 1 / (2 * lam) * Y ^ 2 := by
    have hl2 : 0 < 2 * lam := by positivity
    have key : lam / 2 * X ^ 2 + 1 / (2 * lam) * Y ^ 2 - X * Y =
        (lam * X - Y) ^ 2 / (2 * lam) := by
      field_simp
      ring
    have hnn : 0 ≤ (lam * X - Y) ^ 2 / (2 * lam) := div_nonneg (sq_nonneg _) hl2.le
    linarith
  have h3 : R⁻¹ * X ^ 2 ≤ ψ t ^ 2 * ‖gradient φ y‖ ^ 2 * r ^ 2 * (R⁻¹ * ‖gradient v x‖ ^ 2) := by
    simp only [X]
    have hv2 := verticalDerivative_sq_le_gradient v x
    rw [mul_pow, mul_pow, mul_pow, sq_abs, sq_abs, sq_abs]
    have hR0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
    calc R⁻¹ * (ψ t ^ 2 * ‖gradient φ y‖ ^ 2 * r ^ 2 * vt ^ 2)
        = ψ t ^ 2 * ‖gradient φ y‖ ^ 2 * r ^ 2 * (R⁻¹ * vt ^ 2) := by ring
      _ ≤ ψ t ^ 2 * ‖gradient φ y‖ ^ 2 * r ^ 2 * (R⁻¹ * ‖gradient v x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv2 hR0) (by positivity)
  have h4 : R⁻¹ * Y ^ 2 = φ y ^ 2 * ψ t ^ 2 * (R⁻¹ * ‖hvx‖ ^ 2) / δ ^ 2 := by
    simp only [Y]
    rw [div_pow, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  calc ψ t ^ 2 * (φ y * r) * inner ℝ (gradient φ y) (((δ⁻¹ * R⁻¹) * vt) • hvx)
      ≤ R⁻¹ * (X * Y) := h1
    _ ≤ R⁻¹ * (lam / 2 * X ^ 2 + 1 / (2 * lam) * Y ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hR.le)
    _ = lam / 2 * (R⁻¹ * X ^ 2) + 1 / (2 * lam) * (R⁻¹ * Y ^ 2) := by ring
    _ ≤ lam / 2 * (ψ t ^ 2 * ‖gradient φ y‖ ^ 2 * r ^ 2 * (R⁻¹ * ‖gradient v x‖ ^ 2)) +
        1 / (2 * lam) * (φ y ^ 2 * ψ t ^ 2 * (R⁻¹ * ‖hvx‖ ^ 2) / δ ^ 2) := by
        rw [h4]
        exact add_le_add (mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ lam / 2))
          le_rfl

/-! ## Integrability of the HA6 integrands -/

section Integrability

variable {R δ : ℝ} {v : Space (m + 1) → ℝ} {ψ : ℝ → ℝ}

theorem ha6_continuous_gradient {d : ℕ} {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (gradient φ) :=
  (toDual ℝ (Space d)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)

theorem ha6_hasCompactSupport_gradient {d : ℕ} {φ : Space d → ℝ} (hcφ : HasCompactSupport φ) :
    HasCompactSupport (gradient φ) := by
  refine hcφ.mono' ((subset_tsupport _).trans
    (closure_minimal (fun y hy ↦ ?_) (isClosed_tsupport φ)))
  by_contra hn
  exact hy (by simp [gradient, fderiv_of_notMem_tsupport ℝ hn])

theorem integrable_ha6Kin (hvL : LocallyLipschitz v) {φ : Space m → ℝ} (hφc : Continuous φ)
    (hcφ : HasCompactSupport φ) (hψc : Continuous ψ) (hcψ : HasCompactSupport ψ) (hR : 0 < R) :
    Integrable (ha6Kin R δ v φ ψ) := by
  refine ha6_integrable_grad hvL ?_ (α := fun y ↦ φ y ^ 2 * (R⁻¹ / δ ^ 2))
    (β := fun t ↦ ψ t ^ 2) ((hφc.pow 2).mul continuous_const)
    (ha6_hasCompactSupport_of_zero hcφ fun y h0 ↦ by simp [h0]) (hψc.pow 2)
    (ha6_hasCompactSupport_of_zero hcψ fun t h0 ↦ by simp [h0]) fun x ↦ ?_
  · unfold ha6Kin
    exact ((((hφc.measurable.comp continuous_horizontal.measurable).pow_const 2).mul
      ((hψc.measurable.comp continuous_last.measurable).pow_const 2)).mul
        (measurable_const.mul ((continuous_horizontal.measurable.comp
          (measurable_gradient v)).norm.pow_const 2))).div_const _
  · unfold ha6Kin
    have hR0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left (horizontal_norm_sq_le_gradient v x) hR0
    calc φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 * (R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2) /
          δ ^ 2 ≤ φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 * (R⁻¹ * ‖gradient v x‖ ^ 2) /
          δ ^ 2 := by gcongr
      _ = _ := by ring

theorem integrable_ha6Flux (hvL : LocallyLipschitz v) {ζ : Space m → Space m}
    (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) (hψc : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (hR : 0 < R) (hδ : 0 < δ) :
    Integrable (ha6Flux R δ v ζ ψ) := by
  refine ha6_integrable_grad hvL ?_ (α := fun y ↦ ‖ζ y‖ * (δ⁻¹ * R⁻¹))
    (β := fun t ↦ ψ t ^ 2) (hζ.norm.mul continuous_const)
    (ha6_hasCompactSupport_of_zero hcζ.norm fun y h0 ↦ by simp [h0]) (hψc.pow 2)
    (ha6_hasCompactSupport_of_zero hcψ fun t h0 ↦ by simp [h0]) fun x ↦ ?_
  · unfold ha6Flux
    exact ((hψc.measurable.comp continuous_last.measurable).pow_const 2).mul
      ((hζ.measurable.comp continuous_horizontal.measurable).inner
        (ha6_measurable_flux_vector R δ v))
  · unfold ha6Flux
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ ‖ζ (horizontal x)‖ * (δ⁻¹ * R⁻¹) * ψ (x (Fin.last m)) ^ 2)]
    have h1 := ha6_abs_inner_flux_le hR hδ v (ζ (horizontal x)) x
    calc ψ (x (Fin.last m)) ^ 2 * |inner ℝ (ζ (horizontal x))
          (((δ⁻¹ * R⁻¹) * verticalDerivative v x) • horizontal (gradient v x))|
        ≤ ψ (x (Fin.last m)) ^ 2 * (‖ζ (horizontal x)‖ * (δ⁻¹ * R⁻¹) * ‖gradient v x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = _ := by ring

theorem integrable_ha6Normal (hvL : LocallyLipschitz v) {w : Space m → ℝ} (hw : Continuous w)
    (hcw : HasCompactSupport w) (hψc : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hR : 0 < R) : Integrable (ha6Normal R v w ψ) := by
  refine ha6_integrable_grad hvL ?_ (α := fun y ↦ |w y| * R⁻¹)
    (β := fun t ↦ ψ t ^ 2) (hw.abs.mul continuous_const)
    (ha6_hasCompactSupport_of_zero hcw fun y h0 ↦ by simp [h0]) (hψc.pow 2)
    (ha6_hasCompactSupport_of_zero hcψ fun t h0 ↦ by simp [h0]) fun x ↦ ?_
  · unfold ha6Normal
    exact (((hψc.measurable.comp continuous_last.measurable).pow_const 2).mul
      (hw.measurable.comp continuous_horizontal.measurable)).mul
        (measurable_const.mul ((measurable_verticalDerivative v).pow_const 2))
  · unfold ha6Normal
    have hR0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ R⁻¹ * verticalDerivative v x ^ 2), abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ |w (horizontal x)| * R⁻¹ * ψ (x (Fin.last m)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left (verticalDerivative_sq_le_gradient v x) hR0
    calc ψ (x (Fin.last m)) ^ 2 * |w (horizontal x)| * (R⁻¹ * verticalDerivative v x ^ 2)
        ≤ ψ (x (Fin.last m)) ^ 2 * |w (horizontal x)| * (R⁻¹ * ‖gradient v x‖ ^ 2) := by gcongr
      _ = _ := by ring

theorem integrable_ha6Height (hvL : LocallyLipschitz v) {H φ : Space m → ℝ}
    (hHc : Continuous H) (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hψc : Continuous ψ) (hcψ : HasCompactSupport ψ) (hR : 0 < R) (_hδ : 0 < δ) (a : ℝ) :
    Integrable (ha6Height R δ a v H φ ψ) := by
  obtain ⟨MH, hMH0, hMH⟩ := ha6_exists_bound_on_tsupport hcφ hHc
  have hgφ := ha6_continuous_gradient hφ
  have hcgφ := ha6_hasCompactSupport_gradient hcφ
  refine ha6_integrable_grad hvL ?_ (α := fun y ↦ ‖gradient φ y‖ ^ 2 * R⁻¹)
    (β := fun t ↦ ψ t ^ 2 * (2 * ((t - a) / δ) ^ 2 + 2 * MH ^ 2))
    ((hgφ.norm.pow 2).mul continuous_const)
    (ha6_hasCompactSupport_of_zero hcgφ.norm fun y h0 ↦ by simp [h0])
    ((hψc.pow 2).mul ((continuous_const.mul
      (((continuous_id.sub continuous_const).div_const δ).pow 2)).add continuous_const))
    (ha6_hasCompactSupport_of_zero hcψ fun t h0 ↦ by simp [h0]) fun x ↦ ?_
  · unfold ha6Height
    exact ((((hψc.measurable.comp continuous_last.measurable).pow_const 2).mul
      ((hgφ.measurable.comp continuous_horizontal.measurable).norm.pow_const 2)).mul
        (((((continuous_last.measurable : Measurable (fun x : Space (m + 1) ↦
          (x (Fin.last m) : ℝ))).sub_const a).div_const δ).sub
          (hHc.measurable.comp continuous_horizontal.measurable)).pow_const 2)).mul
            (measurable_const.mul ((measurable_gradient v).norm.pow_const 2))
  · unfold ha6Height
    have hR0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
    by_cases hgx : gradient φ (horizontal x) = 0
    · simp [hgx]
    have hHx : |H (horizontal x)| ≤ MH := by
      apply hMH
      by_contra hn
      exact hgx (by simp [gradient, fderiv_of_notMem_tsupport ℝ hn])
    have hr2 : ((x (Fin.last m) - a) / δ - H (horizontal x)) ^ 2 ≤
        2 * ((x (Fin.last m) - a) / δ) ^ 2 + 2 * MH ^ 2 := by
      have hH2 : H (horizontal x) ^ 2 ≤ MH ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hHx 2
      nlinarith [sq_nonneg ((x (Fin.last m) - a) / δ + H (horizontal x))]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    calc ψ (x (Fin.last m)) ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2 *
          ((x (Fin.last m) - a) / δ - H (horizontal x)) ^ 2 * (R⁻¹ * ‖gradient v x‖ ^ 2)
        ≤ ψ (x (Fin.last m)) ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2 *
          (2 * ((x (Fin.last m) - a) / δ) ^ 2 + 2 * MH ^ 2) * (R⁻¹ * ‖gradient v x‖ ^ 2) := by
          gcongr
      _ = _ := by ring

theorem integrable_ha6Err (hvL : LocallyLipschitz v) {H φ : Space m → ℝ}
    (hHc : Continuous H) (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hψc : Continuous ψ) (hcψ : HasCompactSupport ψ) (hR : 0 < R) (hδ : 0 < δ) (a : ℝ) :
    Integrable (ha6Err R δ a v H φ ψ) := by
  obtain ⟨MH, hMH0, hMH⟩ := ha6_exists_bound_on_tsupport hcφ hHc
  have hgφ := ha6_continuous_gradient hφ
  refine ha6_integrable_grad hvL ?_ (α := fun y ↦ |φ y| * ‖gradient φ y‖ * (δ⁻¹ * R⁻¹))
    (β := fun t ↦ ψ t ^ 2 * (|t - a| / δ + MH))
    ((hφ.continuous.abs.mul hgφ.norm).mul continuous_const)
    (ha6_hasCompactSupport_of_zero hcφ fun y h0 ↦ by simp [h0])
    ((hψc.pow 2).mul (((continuous_id.sub continuous_const).abs.div_const δ).add
      continuous_const))
    (ha6_hasCompactSupport_of_zero hcψ fun t h0 ↦ by simp [h0]) fun x ↦ ?_
  · unfold ha6Err
    exact (((hψc.measurable.comp continuous_last.measurable).pow_const 2).mul
      ((hφ.continuous.measurable.comp continuous_horizontal.measurable).mul
        ((((continuous_last.measurable : Measurable (fun x : Space (m + 1) ↦
          (x (Fin.last m) : ℝ))).sub_const a).div_const δ).sub
          (hHc.measurable.comp continuous_horizontal.measurable)))).mul
            ((hgφ.measurable.comp continuous_horizontal.measurable).inner
              (ha6_measurable_flux_vector R δ v))
  · unfold ha6Err
    by_cases hφx : φ (horizontal x) = 0
    · simp [hφx]
    have hHx : |H (horizontal x)| ≤ MH := hMH _ (subset_tsupport φ hφx)
    have hr : |(x (Fin.last m) - a) / δ - H (horizontal x)| ≤ |x (Fin.last m) - a| / δ + MH := by
      calc |(x (Fin.last m) - a) / δ - H (horizontal x)|
          ≤ |(x (Fin.last m) - a) / δ| + |H (horizontal x)| := abs_sub _ _
        _ ≤ |x (Fin.last m) - a| / δ + MH := by
            rw [abs_div, abs_of_pos hδ]
            linarith
    have h1 := ha6_abs_inner_flux_le hR hδ v (gradient φ (horizontal x)) x
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |φ (horizontal x)| * ‖gradient φ (horizontal x)‖ *
      (δ⁻¹ * R⁻¹) * (ψ (x (Fin.last m)) ^ 2 * (|x (Fin.last m) - a| / δ + MH)))]
    calc ψ (x (Fin.last m)) ^ 2 * (|φ (horizontal x)| *
          |(x (Fin.last m) - a) / δ - H (horizontal x)|) *
          |inner ℝ (gradient φ (horizontal x))
            (((δ⁻¹ * R⁻¹) * verticalDerivative v x) • horizontal (gradient v x))|
        ≤ ψ (x (Fin.last m)) ^ 2 * (|φ (horizontal x)| * (|x (Fin.last m) - a| / δ + MH)) *
          (‖gradient φ (horizontal x)‖ * (δ⁻¹ * R⁻¹) * ‖gradient v x‖ ^ 2) := by
          gcongr
      _ = _ := by ring

theorem integrable_ha6Square (hvL : LocallyLipschitz v) {H φ : Space m → ℝ}
    (hH : ContDiff ℝ 1 H) (hφc : Continuous φ) (hcφ : HasCompactSupport φ)
    (hψc : Continuous ψ) (hcψ : HasCompactSupport ψ) (hR : 0 < R) :
    Integrable (ha6Square R δ v H φ ψ) := by
  have hgH := ha6_continuous_gradient hH
  refine ha6_integrable_grad hvL ?_
    (α := fun y ↦ φ y ^ 2 * (2 * R⁻¹ * ((δ⁻¹) ^ 2 + ‖gradient H y‖ ^ 2)))
    (β := fun t ↦ ψ t ^ 2) ((hφc.pow 2).mul (continuous_const.mul
      (continuous_const.add (hgH.norm.pow 2))))
    (ha6_hasCompactSupport_of_zero hcφ fun y h0 ↦ by simp [h0]) (hψc.pow 2)
    (ha6_hasCompactSupport_of_zero hcψ fun t h0 ↦ by simp [h0]) fun x ↦ ?_
  · unfold ha6Square
    exact (((hφc.measurable.comp continuous_horizontal.measurable).pow_const 2).mul
      ((hψc.measurable.comp continuous_last.measurable).pow_const 2)).mul
        (measurable_const.mul ((((continuous_horizontal.measurable.comp
          (measurable_gradient v)).const_smul δ⁻¹).add ((measurable_verticalDerivative v).smul
            (hgH.measurable.comp continuous_horizontal.measurable))).norm.pow_const 2))
  · unfold ha6Square
    have hR0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have h1 := norm_add_sq_le_two_mul (δ⁻¹ • horizontal (gradient v x))
      (verticalDerivative v x • gradient H (horizontal x))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
      sq_abs] at h1
    have h2 := horizontal_norm_sq_le_gradient v x
    have h3 := verticalDerivative_sq_le_gradient v x
    have h4 : ‖δ⁻¹ • horizontal (gradient v x) +
        verticalDerivative v x • gradient H (horizontal x)‖ ^ 2 ≤
        2 * ((δ⁻¹) ^ 2 + ‖gradient H (horizontal x)‖ ^ 2) * ‖gradient v x‖ ^ 2 := by
      have h5 : (δ⁻¹) ^ 2 * ‖horizontal (gradient v x)‖ ^ 2 ≤ (δ⁻¹) ^ 2 * ‖gradient v x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      have h6 : verticalDerivative v x ^ 2 * ‖gradient H (horizontal x)‖ ^ 2 ≤
          ‖gradient v x‖ ^ 2 * ‖gradient H (horizontal x)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      nlinarith
    calc φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
          (R⁻¹ * ‖δ⁻¹ • horizontal (gradient v x) +
            verticalDerivative v x • gradient H (horizontal x)‖ ^ 2)
        ≤ φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
          (R⁻¹ * (2 * ((δ⁻¹) ^ 2 + ‖gradient H (horizontal x)‖ ^ 2) * ‖gradient v x‖ ^ 2)) := by
          gcongr
      _ = _ := by ring

end Integrability

/-! ## HA6 at one index -/

/-- **HA6 at one index.** For a nonnegative locally Lipschitz `v` with the Modica bound, locally
integrable energy and whole-space stress stationarity, the strong approximation error is
bounded by twice the flux pairing against `φ H ∇φ`, `λ` times the height moment, `λ⁻¹` times
the normalized horizontal kinetic mass, twice the cutoff error, and the two terms produced by
completing the square. -/
theorem integral_ha6Square_le {f : ℝ → ℝ} {R δ a lam : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hlam : 0 < lam) {v : Space (m + 1) → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hvL : LocallyLipschitz v)
    (hmodica : ∀ x, (2 * R)⁻¹ * ‖gradient v x‖ ^ 2 ≤ R * phasePotentialDensity f v x)
    (hiE : ∀ K : Set (Space (m + 1)), IsCompact K →
      IntegrableOn (rescaledPhaseEnergyDensity f R v) K)
    (hstress : ∀ X : Space (m + 1) → Space (m + 1), ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x, (rescaledPhaseEnergyDensity f R v x *
          fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) X x -
        R⁻¹ * inner ℝ (gradient v x) (fderiv ℝ X x (gradient v x)))) = 0)
    {H : Space m → ℝ} (hH : ContDiff ℝ 2 H)
    {φ : Space m → ℝ} {ψ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, ha6Square R δ v H φ ψ x) ≤
      2 * (∫ x, ha6Flux R δ v (fun y ↦ (φ y * H y) • gradient φ y) ψ x) +
      lam * (∫ x, ha6Height R δ a v H φ ψ x) + lam⁻¹ * (∫ x, ha6Kin R δ v φ ψ x) +
      2 * (∫ x, ha6Tail f R δ a v φ ψ x) +
      2 * (∫ x, ha6Flux R δ v (fun y ↦ φ y ^ 2 • gradient H y) ψ x) +
      ∫ x, ha6Normal R v (fun y ↦ φ y ^ 2 * ‖gradient H y‖ ^ 2) ψ x := by
  have hEN (x : Space (m + 1)) :
      0 ≤ rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2 :=
    energy_sub_vertical_sq_nonneg hR hv0 hmodica x
  have hN0 (x : Space (m + 1)) : 0 ≤ R⁻¹ * verticalDerivative v x ^ 2 :=
    mul_nonneg (inv_nonneg.mpr hR.le) (sq_nonneg _)
  have hE0 (x : Space (m + 1)) : 0 ≤ rescaledPhaseEnergyDensity f R v x := by
    linarith [hEN x, hN0 x]
  have hgφ := ha6_continuous_gradient hφ
  have hgH := ha6_continuous_gradient (hH.of_le (by norm_num))
  have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hmt : Measurable (fun x : Space (m + 1) ↦ (x (Fin.last m) : ℝ)) :=
    continuous_last.measurable
  have hmφ : Measurable (fun x : Space (m + 1) ↦ φ (horizontal x)) :=
    hφ.continuous.measurable.comp continuous_horizontal.measurable
  have hmψ : Measurable (fun x : Space (m + 1) ↦ ψ (x (Fin.last m))) :=
    hψ.continuous.measurable.comp hmt
  have hmdψ : Measurable (fun x : Space (m + 1) ↦ deriv ψ (x (Fin.last m))) :=
    hdψ.measurable.comp hmt
  have hmN : Measurable (fun x : Space (m + 1) ↦ R⁻¹ * verticalDerivative v x ^ 2) :=
    measurable_const.mul ((measurable_verticalDerivative v).pow_const 2)
  have hmabs : Measurable (fun x : Space (m + 1) ↦
      |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - a)|) :=
    continuous_abs.measurable.comp ((hmψ.mul hmdψ).mul (hmt.sub_const a))
  have hcsφ2 : HasCompactSupport (fun y ↦ φ y ^ 2) :=
    ha6_hasCompactSupport_of_zero hcφ fun y h0 ↦ by simp [h0]
  have hcsψ2 : HasCompactSupport (fun t ↦ ψ t ^ 2) :=
    ha6_hasCompactSupport_of_zero hcψ fun t h0 ↦ by simp [h0]
  have hβ3c : Continuous (fun t : ℝ ↦ |ψ t * deriv ψ t * (t - a)|) :=
    ((hψ.continuous.mul hdψ).mul (continuous_id.sub continuous_const)).abs
  have hβ3cs : HasCompactSupport (fun t : ℝ ↦ |ψ t * deriv ψ t * (t - a)|) :=
    ha6_hasCompactSupport_of_zero hcψ fun t h0 ↦ by simp [h0]
  -- integrability
  have iKin := integrable_ha6Kin (δ := δ) hvL hφ.continuous hcφ hψ.continuous hcψ hR
  have hζ1 : Continuous (fun y ↦ (φ y * H y) • gradient φ y) :=
    (hφ.continuous.mul hH.continuous).smul hgφ
  have hcζ1 : HasCompactSupport (fun y ↦ (φ y * H y) • gradient φ y) :=
    hcφ.mono' (fun y hy ↦ subset_tsupport φ (fun h0 ↦ hy (by simp [h0])))
  have iF1 := integrable_ha6Flux hvL hζ1 hcζ1 hψ.continuous hcψ hR hδ
  have hζ2 : Continuous (fun y ↦ φ y ^ 2 • gradient H y) := (hφ.continuous.pow 2).smul hgH
  have hcζ2 : HasCompactSupport (fun y ↦ φ y ^ 2 • gradient H y) :=
    hcφ.mono' (fun y hy ↦ subset_tsupport φ (fun h0 ↦ hy (by simp [h0])))
  have iF2 := integrable_ha6Flux hvL hζ2 hcζ2 hψ.continuous hcψ hR hδ
  have hw : Continuous (fun y ↦ φ y ^ 2 * ‖gradient H y‖ ^ 2) :=
    (hφ.continuous.pow 2).mul (hgH.norm.pow 2)
  have hcw : HasCompactSupport (fun y ↦ φ y ^ 2 * ‖gradient H y‖ ^ 2) :=
    ha6_hasCompactSupport_of_zero hcφ fun y h0 ↦ by simp [h0]
  have iNor := integrable_ha6Normal hvL hw hcw hψ.continuous hcψ hR
  have iHei := integrable_ha6Height hvL hH.continuous hφ hcφ hψ.continuous hcψ hR hδ a
  have iErr := integrable_ha6Err hvL hH.continuous hφ hcφ hψ.continuous hcψ hR hδ a
  have iB1 : Integrable (fun x ↦ φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
      (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) := by
    refine ha6_integrable_of_abs_le_prod (α := fun y ↦ φ y ^ 2) (β := fun t ↦ ψ t ^ 2)
      (hφ.continuous.pow 2) hcsφ2 (hψ.continuous.pow 2) hcsψ2 hiE
      (fun K hK ↦ (((hmφ.pow_const 2).mul (hmψ.pow_const 2)).aestronglyMeasurable).mul
        ((hiE K hK).aestronglyMeasurable.sub hmN.aestronglyMeasurable)) fun x ↦ ?_
    have hB : 0 ≤ φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) :=
      mul_nonneg (by positivity) (hEN x)
    rw [abs_of_nonneg hB, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2)]
    exact mul_le_mul_of_nonneg_left (by linarith [hN0 x]) (by positivity)
  have iTail : Integrable (ha6Tail f R δ a v φ ψ) := by
    refine ha6_integrable_of_abs_le_prod (α := fun y ↦ φ y ^ 2 / δ ^ 2)
      (β := fun t ↦ |ψ t * deriv ψ t * (t - a)|) ((hφ.continuous.pow 2).div_const _)
      (ha6_hasCompactSupport_of_zero hcφ fun y h0 ↦ by simp [h0]) hβ3c hβ3cs hiE
      (fun K hK ↦ (((((hmφ.pow_const 2).mul hmabs).aestronglyMeasurable).mul
        (hiE K hK).aestronglyMeasurable).mul_const (δ ^ 2)⁻¹).congr
          (Eventually.of_forall fun x ↦ by simp [ha6Tail, div_eq_mul_inv])) fun x ↦ ?_
    unfold ha6Tail
    have hT : 0 ≤ φ (horizontal x) ^ 2 *
        |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - a)| *
          rescaledPhaseEnergyDensity f R v x / δ ^ 2 := by
      have := hE0 x
      positivity
    rw [abs_of_nonneg hT, abs_of_nonneg (by positivity : (0 : ℝ) ≤ φ (horizontal x) ^ 2 / δ ^ 2 *
      |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - a)|)]
    apply le_of_eq
    ring
  have iB3 : Integrable (fun x ↦ φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) *
      deriv ψ (x (Fin.last m)) * (x (Fin.last m) - a) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) := by
    refine ha6_integrable_of_abs_le_prod (α := fun y ↦ φ y ^ 2)
      (β := fun t ↦ |ψ t * deriv ψ t * (t - a)|) (hφ.continuous.pow 2) hcsφ2 hβ3c hβ3cs hiE
      (fun K hK ↦ ((((hmφ.pow_const 2).mul hmψ).mul hmdψ).mul
        (hmt.sub_const a)).aestronglyMeasurable.mul ((hiE K hK).aestronglyMeasurable.sub
          hmN.aestronglyMeasurable)) fun x ↦ ?_
    have h1 := ha6_tail_le hR hδ a hv0 hmodica φ ψ x
    unfold ha6Tail at h1
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hδ.ne')] at h1
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ φ (horizontal x) ^ 2 *
      |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - a)|)]
    exact h1
  -- FE2 and the chain
  have hFE2 := rescaled_height_stress_identity hvL hiE hstress a hφ hcφ hψ hcψ
  have hsq : (∫ x, ha6Square R δ v H φ ψ x) = (∫ x, ha6Kin R δ v φ ψ x) +
      2 * (∫ x, ha6Flux R δ v (fun y ↦ φ y ^ 2 • gradient H y) ψ x) +
      ∫ x, ha6Normal R v (fun y ↦ φ y ^ 2 * ‖gradient H y‖ ^ 2) ψ x := by
    have i2 : Integrable (fun x ↦
        2 * ha6Flux R δ v (fun y ↦ φ y ^ 2 • gradient H y) ψ x) := iF2.const_mul 2
    have i12 : Integrable (fun x ↦ ha6Kin R δ v φ ψ x +
        2 * ha6Flux R δ v (fun y ↦ φ y ^ 2 • gradient H y) ψ x) := iKin.add i2
    rw [integral_congr_ae (Eventually.of_forall (ha6Square_eq hR hδ v H φ ψ)),
      integral_add i12 iNor, integral_add iKin i2, integral_const_mul]
  have hkinB1 : δ ^ 2 * (∫ x, ha6Kin R δ v φ ψ x) ≤ ∫ x, φ (horizontal x) ^ 2 *
      ψ (x (Fin.last m)) ^ 2 *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2) := by
    rw [← integral_const_mul]
    exact integral_mono (iKin.const_mul _) iB1 (ha6_kin_le hR hδ hv0 hmodica φ ψ)
  have hmid : (∫ x, φ (horizontal x) * ψ (x (Fin.last m)) ^ 2 * (x (Fin.last m) - a) * R⁻¹ *
        verticalDerivative v x * inner ℝ (horizontal (gradient v x)) (gradient φ (horizontal x))) =
      δ ^ 2 * ((∫ x, ha6Flux R δ v (fun y ↦ (φ y * H y) • gradient φ y) ψ x) +
        ∫ x, ha6Err R δ a v H φ ψ x) := by
    rw [integral_congr_ae (Eventually.of_forall (ha6_middle_eq hR hδ a v H φ ψ)),
      integral_const_mul, integral_add iF1 iErr]
  have htail : -(∫ x, φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) *
      (x (Fin.last m) - a) *
        (rescaledPhaseEnergyDensity f R v x - R⁻¹ * verticalDerivative v x ^ 2)) ≤
      δ ^ 2 * ∫ x, ha6Tail f R δ a v φ ψ x := by
    rw [← integral_const_mul]
    exact (neg_le_abs _).trans (abs_integral_le_integral_abs.trans
      (integral_mono iB3.abs (iTail.const_mul _) (ha6_tail_le hR hδ a hv0 hmodica φ ψ)))
  have herr : (∫ x, ha6Err R δ a v H φ ψ x) ≤ lam / 2 * (∫ x, ha6Height R δ a v H φ ψ x) +
      1 / (2 * lam) * ∫ x, ha6Kin R δ v φ ψ x := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iHei.const_mul _) (iKin.const_mul _)]
    exact integral_mono iErr ((iHei.const_mul _).add (iKin.const_mul _))
      (ha6_err_le hR hδ hlam a v H φ ψ)
  have hkin : (∫ x, ha6Kin R δ v φ ψ x) ≤
      2 * (∫ x, ha6Flux R δ v (fun y ↦ (φ y * H y) • gradient φ y) ψ x) +
      2 * (∫ x, ha6Err R δ a v H φ ψ x) + 2 * ∫ x, ha6Tail f R δ a v φ ψ x := by
    have hδ2 : 0 < δ ^ 2 := by positivity
    have h2 := hkinB1.trans_eq hFE2
    rw [hmid] at h2
    have h1 : δ ^ 2 * (∫ x, ha6Kin R δ v φ ψ x) ≤ δ ^ 2 *
        (2 * (∫ x, ha6Flux R δ v (fun y ↦ (φ y * H y) • gradient φ y) ψ x) +
          2 * (∫ x, ha6Err R δ a v H φ ψ x) + 2 * ∫ x, ha6Tail f R δ a v φ ψ x) := by
      nlinarith [htail]
    exact le_of_mul_le_mul_left h1 hδ2
  have hlinv : 2 * (1 / (2 * lam)) = lam⁻¹ := by field_simp
  rw [hsq]
  have h3 : (∫ x, ha6Kin R δ v φ ψ x) ≤
      2 * (∫ x, ha6Flux R δ v (fun y ↦ (φ y * H y) • gradient φ y) ψ x) +
      lam * (∫ x, ha6Height R δ a v H φ ψ x) + lam⁻¹ * (∫ x, ha6Kin R δ v φ ψ x) +
      2 * ∫ x, ha6Tail f R δ a v φ ψ x := by
    rw [← hlinv]
    nlinarith [herr, hkin]
  linarith

/-! ## HA6 along a sequence -/

/-- **HA6 along a sequence.** Let `H` be `C²` and harmonic on an open set containing the support
of the horizontal cutoff `φ`. Suppose that along a sequence of rescaled functions the normalized
horizontal kinetic masses are eventually bounded, the height moments and the cutoff errors tend to
zero, the two flux pairings converge to `-σ c ∫ ⟪ζ, ∇H⟫`, and the normal kinetic pairing is
asymptotically at most `σ c ∫ φ² |∇H|²`. Then the strong approximation error tends to zero: by
Green's identity the limits of the flux terms, `σ c A` and `-2 σ c A` (`A = ∫ φ² |∇H|²`), cancel
the normal kinetic limit `σ c A`, and the parameter `λ` of the height error is chosen after the
tolerance. -/
theorem tendsto_integral_ha6Square_of_limits {f : ℝ → ℝ} {R δ a : ℕ → ℝ}
    {v : ℕ → Space (m + 1) → ℝ} (hR : ∀ j, 0 < R j) (hδ : ∀ j, 0 < δ j)
    (hv0 : ∀ j x, 0 ≤ v j x) (hvL : ∀ j, LocallyLipschitz (v j))
    (hmodica : ∀ j x, (2 * R j)⁻¹ * ‖gradient (v j) x‖ ^ 2 ≤
      R j * phasePotentialDensity f (v j) x)
    (hiE : ∀ j, ∀ K : Set (Space (m + 1)), IsCompact K →
      IntegrableOn (rescaledPhaseEnergyDensity f (R j) (v j)) K)
    (hstress : ∀ j, ∀ X : Space (m + 1) → Space (m + 1), ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x, (rescaledPhaseEnergyDensity f (R j) (v j) x *
          fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) X x -
        (R j)⁻¹ * inner ℝ (gradient (v j) x) (fderiv ℝ X x (gradient (v j) x)))) = 0)
    {U : Set (Space m)} (hU : IsOpen U) {H : Space m → ℝ} (hH : ContDiff ℝ 2 H)
    (hΔ : ∀ y ∈ U, Δ H y = 0) {φ : Space m → ℝ} {ψ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (hψ : ContDiff ℝ 1 ψ)
    (hcψ : HasCompactSupport ψ) {σ c B : ℝ}
    (hKin : ∀ᶠ j in atTop, (∫ x, ha6Kin (R j) (δ j) (v j) φ ψ x) ≤ B)
    (hHei : Tendsto (fun j ↦ ∫ x, ha6Height (R j) (δ j) (a j) (v j) H φ ψ x) atTop (𝓝 0))
    (hF1 : Tendsto (fun j ↦ ∫ x, ha6Flux (R j) (δ j) (v j)
        (fun y ↦ (φ y * H y) • gradient φ y) ψ x) atTop
      (𝓝 (-(σ * c) * ∫ y, inner ℝ ((φ y * H y) • gradient φ y) (gradient H y))))
    (hF2 : Tendsto (fun j ↦ ∫ x, ha6Flux (R j) (δ j) (v j)
        (fun y ↦ φ y ^ 2 • gradient H y) ψ x) atTop
      (𝓝 (-(σ * c) * ∫ y, inner ℝ (φ y ^ 2 • gradient H y) (gradient H y))))
    (hTail : Tendsto (fun j ↦ ∫ x, ha6Tail f (R j) (δ j) (a j) (v j) φ ψ x) atTop (𝓝 0))
    (hNor : ∀ η > 0, ∀ᶠ j in atTop, (∫ x, ha6Normal (R j) (v j)
        (fun y ↦ φ y ^ 2 * ‖gradient H y‖ ^ 2) ψ x) ≤
      σ * c * (∫ y, φ y ^ 2 * ‖gradient H y‖ ^ 2) + η) :
    Tendsto (fun j ↦ ∫ x, ha6Square (R j) (δ j) (v j) H φ ψ x) atTop (𝓝 0) := by
  have hgreen := integral_sq_mul_norm_gradient_sq_of_harmonic hU hH hΔ hφ hcφ hφU
  have hL1 : (∫ y, inner ℝ ((φ y * H y) • gradient φ y) (gradient H y)) =
      -((∫ y, φ y ^ 2 * ‖gradient H y‖ ^ 2) / 2) := by
    have hfun : (fun y ↦ inner ℝ ((φ y * H y) • gradient φ y) (gradient H y)) =
        fun y ↦ φ y * H y * inner ℝ (gradient H y) (gradient φ y) := by
      funext y
      rw [real_inner_smul_left, real_inner_comm]
    rw [hfun]
    linarith [hgreen]
  have hL2 : (∫ y, inner ℝ (φ y ^ 2 • gradient H y) (gradient H y)) =
      ∫ y, φ y ^ 2 * ‖gradient H y‖ ^ 2 := by
    congr 1
    funext y
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [hL1] at hF1
  rw [hL2] at hF2
  set A : ℝ := ∫ y, φ y ^ 2 * ‖gradient H y‖ ^ 2 with hA
  have hSq0 (j : ℕ) : 0 ≤ ∫ x, ha6Square (R j) (δ j) (v j) H φ ψ x := by
    refine integral_nonneg fun x ↦ ?_
    have := hR j
    unfold ha6Square
    positivity
  have hKin0 (j : ℕ) : 0 ≤ ∫ x, ha6Kin (R j) (δ j) (v j) φ ψ x := by
    refine integral_nonneg fun x ↦ ?_
    have := hR j
    unfold ha6Kin
    positivity
  refine tendsto_order.2 ⟨fun b hb ↦ Eventually.of_forall fun j ↦ hb.trans_le (hSq0 j),
    fun b hb ↦ ?_⟩
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = b / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hB1 : 0 < |B| + 1 := by positivity
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = 6 * (|B| + 1) / η := ⟨_, rfl⟩
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hlamB : lam⁻¹ * (|B| + 1) = η / 6 := by
    rw [hlamdef]
    field_simp
  have e1 : ∀ᶠ j in atTop, 2 * (∫ x, ha6Flux (R j) (δ j) (v j)
      (fun y ↦ (φ y * H y) • gradient φ y) ψ x) < σ * c * A + η / 6 := by
    refine (hF1.const_mul 2).eventually_lt_const ?_
    have : 2 * (-(σ * c) * -(A / 2)) = σ * c * A := by ring
    rw [this]
    linarith
  have e2 : ∀ᶠ j in atTop, lam * (∫ x, ha6Height (R j) (δ j) (a j) (v j) H φ ψ x) < η / 6 := by
    refine (hHei.const_mul lam).eventually_lt_const ?_
    rw [mul_zero]
    positivity
  have e3 : ∀ᶠ j in atTop, 2 * (∫ x, ha6Tail f (R j) (δ j) (a j) (v j) φ ψ x) < η / 6 := by
    refine (hTail.const_mul 2).eventually_lt_const ?_
    rw [mul_zero]
    positivity
  have e4 : ∀ᶠ j in atTop, 2 * (∫ x, ha6Flux (R j) (δ j) (v j)
      (fun y ↦ φ y ^ 2 • gradient H y) ψ x) < -2 * (σ * c * A) + η / 6 := by
    refine (hF2.const_mul 2).eventually_lt_const ?_
    have : 2 * (-(σ * c) * A) = -2 * (σ * c * A) := by ring
    rw [this]
    linarith
  filter_upwards [e1, e2, e3, e4, hKin, hNor (η / 6) (by positivity)] with j h1 h2 h3 h4 h5 h6
  have hmain := integral_ha6Square_le (a := a j) (hR j) (hδ j) hlam (hv0 j) (hvL j) (hmodica j)
    (hiE j) (hstress j) hH hφ hcφ hψ hcψ
  have hk : lam⁻¹ * (∫ x, ha6Kin (R j) (δ j) (v j) φ ψ x) ≤ η / 6 := by
    rw [← hlamB]
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self B]) (inv_nonneg.mpr hlam.le)
  linarith

/-! ## Cylinder bounds for the HA6 terms -/

/-- Comparison with a set integral: if `0 ≤ G`, `G ≤ C F` on a measurable set `S`, `G = 0` off
`S` and `F` is integrable on `S`, then `∫ G ≤ C ∫_S F`. -/
theorem ha6_integral_le_setIntegral {d : ℕ} {G F : Space d → ℝ} {S : Set (Space d)}
    (hS : MeasurableSet S) (hF : IntegrableOn F S) {C : ℝ} (hG0 : ∀ x, 0 ≤ G x)
    (hGS : ∀ x ∈ S, G x ≤ C * F x) (hGc : ∀ x ∉ S, G x = 0) :
    (∫ x, G x) ≤ C * ∫ x in S, F x := by
  rw [← integral_const_mul, ← integral_indicator hS]
  refine integral_mono_of_nonneg (Eventually.of_forall hG0)
    (IntegrableOn.integrable_indicator (f := fun x ↦ C * F x) (hF.const_mul C) hS)
    (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx]
    exact hGS x hx
  · rw [indicator_of_notMem hx, hGc x hx]

theorem ha6_gradient_eq_zero_of_notMem_tsupport {d : ℕ} {φ : Space d → ℝ} {y : Space d}
    (hy : y ∉ tsupport φ) : gradient φ y = 0 := by
  simp [gradient, fderiv_of_notMem_tsupport ℝ hy]

theorem ha6_mem_closedBall_of_mem_tiltCylinder {z : Space (m + 1)} {r : ℝ}
    (hz : z ∈ tiltCylinder (verticalDirection m) r) : z ∈ closedBall (0 : Space (m + 1)) (2 * r) := by
  rw [mem_closedBall, dist_zero_right]
  have h1 := (norm_lt_of_mem_tiltCylinder (norm_verticalDirection m) hz).le
  have hr : 0 ≤ r := (abs_nonneg _).trans ((mem_tiltCylinder_vertical_iff.mp hz).2.le)
  have hs : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  nlinarith

theorem ha6_tiltCylinder_subset_closedBall (r : ℝ) :
    tiltCylinder (verticalDirection m) r ⊆ closedBall (0 : Space (m + 1)) (2 * r) :=
  fun _ hz ↦ ha6_mem_closedBall_of_mem_tiltCylinder hz

/-- The height moment with cutoffs is bounded by the plain height moment on a vertical cylinder
containing the supports. -/
theorem integral_ha6Height_le_cylinder {R δ a r Cg : ℝ} (hR : 0 < R) {v : Space (m + 1) → ℝ}
    (hvL : LocallyLipschitz v) {H φ : Space m → ℝ} {ψ : ℝ → ℝ} (hHc : Continuous H)
    (hψ1 : ∀ t, ψ t ^ 2 ≤ 1) (hCg : ∀ y, ‖gradient φ y‖ ^ 2 ≤ Cg)
    (hφr : ∀ y, r ≤ ‖y‖ → gradient φ y = 0) (hψr : ∀ t, r ≤ |t| → ψ t = 0) :
    (∫ x, ha6Height R δ a v H φ ψ x) ≤
      Cg * ∫ z in tiltCylinder (verticalDirection m) r,
        ((z (Fin.last m) - a) / δ - H (horizontal z)) ^ 2 * (R⁻¹ * ‖gradient v z‖ ^ 2) := by
  have hS : MeasurableSet (tiltCylinder (verticalDirection m) r) :=
    (isOpen_tiltCylinder _ _).measurableSet
  refine ha6_integral_le_setIntegral hS ?_ (fun x ↦ ?_) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hcl : Continuous (fun z : Space (m + 1) ↦ (z (Fin.last m) : ℝ)) := continuous_last
    have hc : Continuous (fun z : Space (m + 1) ↦ ((z (Fin.last m) - a) / δ - H (horizontal z)) ^ 2) :=
      (((hcl.sub continuous_const).div_const δ).sub
        (hHc.comp continuous_horizontal)).pow 2
    obtain ⟨C0, hC0⟩ := (isCompact_closedBall (0 : Space (m + 1)) (2 * r)).exists_bound_of_continuousOn
      hc.continuousOn
    refine integrableOn_of_abs_le_mul_gradient_sq hvL ?_ hS
      (isBounded_tiltCylinder (norm_verticalDirection m) r) (C := C0 * R⁻¹) fun z hz ↦ ?_
    · exact hc.measurable.mul (measurable_const.mul
        ((measurable_gradient v).norm.pow_const 2))
    · have h1 := hC0 z (ha6_mem_closedBall_of_mem_tiltCylinder hz)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h1
      rw [abs_of_nonneg (by positivity)]
      have hR0 : 0 ≤ R⁻¹ * ‖gradient v z‖ ^ 2 := by positivity
      calc ((z (Fin.last m) - a) / δ - H (horizontal z)) ^ 2 * (R⁻¹ * ‖gradient v z‖ ^ 2)
          ≤ C0 * (R⁻¹ * ‖gradient v z‖ ^ 2) := mul_le_mul_of_nonneg_right h1 hR0
        _ = C0 * R⁻¹ * ‖gradient v z‖ ^ 2 := by ring
  · unfold ha6Height
    positivity
  · have hF0 : 0 ≤ ((x (Fin.last m) - a) / δ - H (horizontal x)) ^ 2 *
        (R⁻¹ * ‖gradient v x‖ ^ 2) := by positivity
    have hpq : ψ (x (Fin.last m)) ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2 ≤ Cg :=
      calc ψ (x (Fin.last m)) ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2
          ≤ 1 * ‖gradient φ (horizontal x)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hψ1 _) (sq_nonneg _)
        _ ≤ Cg := by rw [one_mul]; exact hCg _
    unfold ha6Height
    calc ψ (x (Fin.last m)) ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2 *
          ((x (Fin.last m) - a) / δ - H (horizontal x)) ^ 2 * (R⁻¹ * ‖gradient v x‖ ^ 2)
        = (ψ (x (Fin.last m)) ^ 2 * ‖gradient φ (horizontal x)‖ ^ 2) *
          (((x (Fin.last m) - a) / δ - H (horizontal x)) ^ 2 * (R⁻¹ * ‖gradient v x‖ ^ 2)) := by
          ring
      _ ≤ Cg * (((x (Fin.last m) - a) / δ - H (horizontal x)) ^ 2 *
          (R⁻¹ * ‖gradient v x‖ ^ 2)) := mul_le_mul_of_nonneg_right hpq hF0
  · rw [mem_tiltCylinder_vertical_iff, not_and_or, not_lt, not_lt] at hx
    unfold ha6Height
    rcases hx with hx | hx
    · rw [hφr _ hx, norm_zero]
      ring
    · rw [hψr _ hx]
      ring

/-- The cutoff error is bounded by the energy of the cylinder away from the horizontal plane. -/
theorem integral_ha6Tail_le_cylinder {f : ℝ → ℝ} {R δ a r c Cψ : ℝ} {v : Space (m + 1) → ℝ}
    (hE0 : ∀ x, 0 ≤ rescaledPhaseEnergyDensity f R v x)
    (hiE : ∀ K : Set (Space (m + 1)), IsCompact K →
      IntegrableOn (rescaledPhaseEnergyDensity f R v) K)
    {φ : Space m → ℝ} {ψ : ℝ → ℝ} (hφ1 : ∀ y, φ y ^ 2 ≤ 1)
    (hCψ : ∀ t, |ψ t * deriv ψ t| ≤ Cψ) (hφr : ∀ y, r ≤ ‖y‖ → φ y = 0)
    (hψr : ∀ t, r ≤ |t| → ψ t = 0) (hdψ : ∀ t, |t| < c → deriv ψ t = 0) :
    (∫ x, ha6Tail f R δ a v φ ψ x) ≤ Cψ * (r + |a|) * ((δ⁻¹) ^ 2 *
      ∫ z in tiltCylinder (verticalDirection m) r ∩ {z | c ≤ |z (Fin.last m)|},
        rescaledPhaseEnergyDensity f R v z) := by
  have hS : MeasurableSet (tiltCylinder (verticalDirection m) r ∩
      {z : Space (m + 1) | c ≤ |z (Fin.last m)|}) :=
    (isOpen_tiltCylinder _ _).measurableSet.inter
      (isClosed_le continuous_const (continuous_abs.comp continuous_last)).measurableSet
  have hCψ0 : 0 ≤ Cψ := (abs_nonneg _).trans (hCψ 0)
  rw [← integral_const_mul]
  refine ha6_integral_le_setIntegral hS ?_ (fun x ↦ ?_) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · exact (((hiE _ (isCompact_closedBall (0 : Space (m + 1)) (2 * r))).mono_set
      (inter_subset_left.trans (ha6_tiltCylinder_subset_closedBall r))).const_mul _)
  · unfold ha6Tail
    have := hE0 x
    positivity
  · obtain ⟨hxQ, -⟩ := hx
    rw [mem_tiltCylinder_vertical_iff] at hxQ
    have ht : |x (Fin.last m) - a| ≤ r + |a| := by
      have := abs_sub (x (Fin.last m)) a
      linarith [hxQ.2]
    have h1 : |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - a)| ≤
        Cψ * (r + |a|) := by
      rw [abs_mul]
      exact mul_le_mul (hCψ _) ht (abs_nonneg _) hCψ0
    have hE := hE0 x
    unfold ha6Tail
    calc φ (horizontal x) ^ 2 *
          |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - a)| *
          rescaledPhaseEnergyDensity f R v x / δ ^ 2
        = (φ (horizontal x) ^ 2 *
          |ψ (x (Fin.last m)) * deriv ψ (x (Fin.last m)) * (x (Fin.last m) - a)|) *
          ((δ⁻¹) ^ 2 * rescaledPhaseEnergyDensity f R v x) := by ring
      _ ≤ (1 * (Cψ * (r + |a|))) * ((δ⁻¹) ^ 2 * rescaledPhaseEnergyDensity f R v x) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul (hφ1 _) h1 (abs_nonneg _) zero_le_one)
            (by positivity)
      _ = Cψ * (r + |a|) * ((δ⁻¹) ^ 2 * rescaledPhaseEnergyDensity f R v x) := by ring
  · rw [mem_inter_iff, mem_tiltCylinder_vertical_iff, not_and_or, not_and_or, not_lt, not_lt,
      mem_ofPred_eq, not_le] at hx
    unfold ha6Tail
    rcases hx with (hx | hx) | hx
    · rw [hφr _ hx]
      ring
    · rw [hψr _ hx]
      simp
    · rw [hdψ _ hx]
      simp

/-- The normal kinetic pairing with cutoffs is bounded by the weighted normal kinetic mass of a
vertical cylinder containing the supports. -/
theorem integral_ha6Normal_le_cylinder {R r : ℝ} (hR : 0 < R) {v : Space (m + 1) → ℝ}
    (hvL : LocallyLipschitz v) {w : Space m → ℝ} {ψ : ℝ → ℝ} (hw : Continuous w)
    (hw0 : ∀ y, 0 ≤ w y) (hψ1 : ∀ t, ψ t ^ 2 ≤ 1) (hwr : ∀ y, r ≤ ‖y‖ → w y = 0)
    (hψr : ∀ t, r ≤ |t| → ψ t = 0) :
    (∫ x, ha6Normal R v w ψ x) ≤ ∫ z in tiltCylinder (verticalDirection m) r,
      verticalDerivative v z ^ 2 / R * w (horizontal z) := by
  have hS : MeasurableSet (tiltCylinder (verticalDirection m) r) :=
    (isOpen_tiltCylinder _ _).measurableSet
  have key := ha6_integral_le_setIntegral (C := 1) (G := ha6Normal R v w ψ)
    (F := fun z ↦ verticalDerivative v z ^ 2 / R * w (horizontal z)) hS ?_ (fun x ↦ ?_)
    (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rwa [one_mul] at key
  · obtain ⟨C0, hC0⟩ := (isCompact_closedBall (0 : Space (m + 1)) (2 * r)).exists_bound_of_continuousOn
      (hw.comp continuous_horizontal).continuousOn
    refine integrableOn_of_abs_le_mul_gradient_sq hvL ?_ hS
      (isBounded_tiltCylinder (norm_verticalDirection m) r) (C := R⁻¹ * C0) fun z hz ↦ ?_
    · exact (((measurable_verticalDerivative v).pow_const 2).div_const R).mul
        (hw.measurable.comp continuous_horizontal.measurable)
    · have h1 := hC0 z (ha6_mem_closedBall_of_mem_tiltCylinder hz)
      rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hw0 _)] at h1
      have h0 := hw0 (horizontal z)
      rw [abs_of_nonneg (by positivity)]
      have h2 := verticalDerivative_sq_le_gradient v z
      have hR0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
      calc verticalDerivative v z ^ 2 / R * w (horizontal z)
          = R⁻¹ * (verticalDerivative v z ^ 2 * w (horizontal z)) := by ring
        _ ≤ R⁻¹ * (‖gradient v z‖ ^ 2 * C0) := by
            gcongr
        _ = R⁻¹ * C0 * ‖gradient v z‖ ^ 2 := by ring
  · unfold ha6Normal
    have := hw0 (horizontal x)
    positivity
  · unfold ha6Normal
    have h0 := hw0 (horizontal x)
    have hN : 0 ≤ w (horizontal x) * (R⁻¹ * verticalDerivative v x ^ 2) := by positivity
    calc ψ (x (Fin.last m)) ^ 2 * w (horizontal x) * (R⁻¹ * verticalDerivative v x ^ 2)
        = ψ (x (Fin.last m)) ^ 2 * (w (horizontal x) * (R⁻¹ * verticalDerivative v x ^ 2)) := by
          ring
      _ ≤ 1 * (w (horizontal x) * (R⁻¹ * verticalDerivative v x ^ 2)) :=
          mul_le_mul_of_nonneg_right (hψ1 _) hN
      _ = 1 * (verticalDerivative v x ^ 2 / R * w (horizontal x)) := by ring
  · rw [mem_tiltCylinder_vertical_iff, not_and_or, not_lt, not_lt] at hx
    unfold ha6Normal
    rcases hx with hx | hx
    · rw [hwr _ hx]
      ring
    · rw [hψr _ hx]
      ring

/-- The normalized horizontal kinetic mass with cutoffs supported in `Q₂` is controlled by the
HA0 cylinder tilt `𝓔(2, e_n)`. -/
theorem integral_ha6Kin_le_cylinderTilt {R δ : ℝ} (hR : 0 < R) {v : Space (m + 1) → ℝ}
    (hvL : LocallyLipschitz v) {φ : Space m → ℝ} {ψ : ℝ → ℝ} (hφ1 : ∀ y, φ y ^ 2 ≤ 1)
    (hψ1 : ∀ t, ψ t ^ 2 ≤ 1) (hφr : ∀ y, 2 ≤ ‖y‖ → φ y = 0) (hψr : ∀ t, 2 ≤ |t| → ψ t = 0) :
    (∫ x, ha6Kin R δ v φ ψ x) ≤
      (δ⁻¹) ^ 2 * (2 ^ m * cylinderTilt R v 2 (verticalDirection m)) := by
  have hS : MeasurableSet (tiltCylinder (verticalDirection m) 2) :=
    (isOpen_tiltCylinder _ _).measurableSet
  have hct : (2 : ℝ) ^ m * cylinderTilt R v 2 (verticalDirection m) =
      ∫ z in tiltCylinder (verticalDirection m) 2, diffuseTiltDensity R v (verticalDirection m) z := by
    unfold cylinderTilt
    rw [← mul_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
  rw [hct]
  refine ha6_integral_le_setIntegral hS ?_ (fun x ↦ ?_) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · refine integrableOn_of_abs_le_mul_gradient_sq hvL ?_ hS
      (isBounded_tiltCylinder (norm_verticalDirection m) 2) (C := R⁻¹) fun z _ ↦ ?_
    · unfold diffuseTiltDensity
      exact (((measurable_gradient v).norm.pow_const 2).sub
        (((measurable_gradient v).inner measurable_const).pow_const 2)).div_const R
    · rw [diffuseTiltDensity_vertical_eq, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (horizontal_norm_sq_le_gradient v z)
        (inv_nonneg.mpr hR.le)
  · unfold ha6Kin
    positivity
  · rw [diffuseTiltDensity_vertical_eq]
    unfold ha6Kin
    have hK0 : 0 ≤ R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2 := by positivity
    have hpq : φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 ≤ 1 :=
      calc φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 ≤ 1 * 1 :=
            mul_le_mul (hφ1 _) (hψ1 _) (sq_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2 *
          (R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2) / δ ^ 2
        = (δ⁻¹) ^ 2 * ((φ (horizontal x) ^ 2 * ψ (x (Fin.last m)) ^ 2) *
          (R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2)) := by ring
      _ ≤ (δ⁻¹) ^ 2 * (1 * (R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2)) := by
          gcongr
      _ = (δ⁻¹) ^ 2 * (R⁻¹ * ‖horizontal (gradient v x)‖ ^ 2) := by ring
  · rw [mem_tiltCylinder_vertical_iff, not_and_or, not_lt, not_lt] at hx
    unfold ha6Kin
    rcases hx with hx | hx
    · rw [hφr _ hx]
      ring
    · rw [hψr _ hx]
      ring

/-- On a cylinder where both cutoffs equal `1`, the strong approximation error dominates the
plain integral of `ε |∇_y v / δ + ∂ₜ v ∇H|²`. -/
theorem setIntegral_cylinder_le_integral_ha6Square {R δ s : ℝ} (hR : 0 < R)
    {v : Space (m + 1) → ℝ} (hvL : LocallyLipschitz v) {H φ : Space m → ℝ} {ψ : ℝ → ℝ}
    (hH : ContDiff ℝ 1 H) (hφc : Continuous φ) (hcφ : HasCompactSupport φ) (hψc : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (hφ1 : ∀ y, ‖y‖ < s → φ y = 1)
    (hψ1 : ∀ t, |t| < s → ψ t = 1) :
    (∫ z in tiltCylinder (verticalDirection m) s,
        ‖δ⁻¹ • horizontal (gradient v z) + verticalDerivative v z • gradient H (horizontal z)‖ ^ 2 /
          R) ≤ ∫ x, ha6Square R δ v H φ ψ x := by
  have hS : MeasurableSet (tiltCylinder (verticalDirection m) s) :=
    (isOpen_tiltCylinder _ _).measurableSet
  calc (∫ z in tiltCylinder (verticalDirection m) s,
        ‖δ⁻¹ • horizontal (gradient v z) + verticalDerivative v z • gradient H (horizontal z)‖ ^ 2 /
          R)
      = ∫ z in tiltCylinder (verticalDirection m) s, ha6Square R δ v H φ ψ z := by
        refine setIntegral_congr_fun hS fun z hz ↦ ?_
        rw [mem_tiltCylinder_vertical_iff] at hz
        unfold ha6Square
        rw [hφ1 _ hz.1, hψ1 _ hz.2]
        ring
    _ ≤ ∫ x, ha6Square R δ v H φ ψ x :=
        setIntegral_le_integral (integrable_ha6Square hvL hH hφc hcφ hψc hcψ hR)
          (Eventually.of_forall fun x ↦ by unfold ha6Square; positivity)

/-! ## HA6 along the HA11 contradiction sequences -/

/-- **The inputs of HA6 along HA11 contradiction sequences.** For every sequence of free-boundary
centers `x j`, scales `R j → ∞`, rotations `Q j` and tilt scales `δ j → 0` with `R j δ j → ∞`
whose rotated rescalings `v_j z = zeroExtension g u (x j + R j • Q j z)` have vertical HA0
cylinder tilt `𝓔(2, e_n) = δ j ²`, there are a subsequence `φ`, a `C²` function `H` harmonic on
an open set `U ⊇ B̄_{1/2}` with `L²` and Dirichlet bounds `M` on `B_{1/2}`, and height centers
`a j → 0` such that, writing `ρ_j = ε |∇v_j|²` (`ε = R⁻¹`):

* **(HA6.1)** the weighted height approximation
  `∫_{Q_{1/2}} ((t - a_j)/δ_j - H(y))² ρ_j → 0` (blueprint HA2–HA5, HA9.e, HA10);
* **(HA4)** the normalized flux `F_j = ε ∂ₜ v_j ∇_y v_j / δ_j` converges weakly to
  `-σ ∇H ⊗ δ_{t=0}` against product test functions supported in `Q_{1/2}`;
* **(FE3/HA8 tails)** the energy of `Q_{1/2}` at distance `≥ c` from the horizontal plane is
  `o(δ_j²)` for every `c > 0`;
* **(normal kinetic bound)** the weighted normal kinetic mass `∫_{Q_s} ε (∂ₜ v_j)² w(y)` is
  asymptotically at most `σ ∫_{B_s} w` (energy concentrates on the plane with density `σ`). -/
def HasHarmonicHeightData (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (f : ℝ → ℝ)
    (σ M : ℝ) : Prop :=
  ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ),
    (∀ j, x j ∈ frontier (epigraph g)) → (∀ j, 0 < R j) → Tendsto R atTop atTop →
    (∀ j, 0 < δ j) → Tendsto δ atTop (𝓝 0) → Tendsto (fun j ↦ R j * δ j) atTop atTop →
    (∀ j, cylinderTilt (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) 2
      (verticalDirection m) = δ j ^ 2) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (H : Space m → ℝ) (U : Set (Space m)) (a : ℕ → ℝ),
      IsOpen U ∧ closedBall (0 : Space m) (1 / 2) ⊆ U ∧ ContDiff ℝ 2 H ∧
      (∀ y ∈ U, Δ H y = 0) ∧
      (∫ y in ball (0 : Space m) (1 / 2), H y ^ 2) ≤ M ∧
      (∫ y in ball (0 : Space m) (1 / 2), ‖gradient H y‖ ^ 2) ≤ M ∧
      Tendsto a atTop (𝓝 0) ∧
      Tendsto (fun j ↦ ∫ z in tiltCylinder (verticalDirection m) (1 / 2),
        ((z (Fin.last m) - a j) / δ (φ j) - H (horizontal z)) ^ 2 *
          ((R (φ j))⁻¹ * ‖gradient (fun z ↦ zeroExtension g u
            (x (φ j) + R (φ j) • Q (φ j) z)) z‖ ^ 2)) atTop (𝓝 0) ∧
      (∀ ζ : Space m → Space m, Continuous ζ → tsupport ζ ⊆ ball (0 : Space m) (1 / 2) →
        ∀ ψ : ℝ → ℝ, Continuous ψ → tsupport ψ ⊆ Ioo (-(1 / 2)) (1 / 2) →
        Tendsto (fun j ↦ ∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z))
          (((δ (φ j))⁻¹ * (R (φ j))⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u
              (x (φ j) + R (φ j) • Q (φ j) z)) z) •
            horizontal (gradient (fun z ↦ zeroExtension g u
              (x (φ j) + R (φ j) • Q (φ j) z)) z))) atTop
          (𝓝 (-(σ * ψ 0) * ∫ y, inner ℝ (ζ y) (gradient H y)))) ∧
      (∀ c > 0, Tendsto (fun j ↦ (δ (φ j))⁻¹ ^ 2 *
        ∫ z in tiltCylinder (verticalDirection m) (1 / 2) ∩ {z | c ≤ |z (Fin.last m)|},
          rescaledPhaseEnergyDensity f (R (φ j)) (fun z ↦ zeroExtension g u
            (x (φ j) + R (φ j) • Q (φ j) z)) z) atTop (𝓝 0)) ∧
      ∀ s ∈ Ioc (0 : ℝ) (1 / 2), ∀ w : Space m → ℝ, Continuous w → (∀ y, 0 ≤ w y) →
        ∀ η > 0, ∀ᶠ j in atTop,
          (∫ z in tiltCylinder (verticalDirection m) s,
            verticalDerivative (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) z ^ 2 /
              R (φ j) * w (horizontal z)) ≤ σ * (∫ y in ball (0 : Space m) s, w y) + η

/-- **HA6 assembled.** The HA6 inputs along HA11 sequences give the strong weighted gradient
convergence `∫_{Q_{1/4}} ε |∇_y v_j / δ_j + ∂ₜ v_j ∇H|² → 0` required by HA7, i.e. the harmonic
approximation interface `HasHarmonicApproximation`. The cutoffs are smooth bumps equal to `1` on
`B̄_{1/4}` and `[-1/4, 1/4]` and supported in `B̄_{3/8}` and `[-3/8, 3/8]`; the normalized
horizontal kinetic masses are bounded by `2ᵐ` through the cylinder tilt normalization. -/
theorem RigidityHypotheses.hasHarmonicApproximation_of_heightData {f : ℝ → ℝ} {κ : ℝ}
    {g : Space m → ℝ} {u : Space (m + 1) → ℝ} (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {σ M : ℝ} (hdata : HasHarmonicHeightData g u f σ M) :
    HasHarmonicApproximation g u σ M := by
  intro x R Q δ hx hR hRt hδ hδ0 hRδ htilt
  obtain ⟨φ, hφ, H, U, a, hU, hBU, hH, hΔ, hM1, hM2, ha0, hI1, hI2, hI3, hI4⟩ :=
    hdata x R Q δ hx hR hRt hδ hδ0 hRδ htilt
  refine ⟨φ, hφ, H, U, hU, hBU, hH, hΔ, hM1, hM2, ?_, fun s hs w hw hw0 η hη ↦
    hI4 s ⟨hs.1, hs.2.trans (by norm_num)⟩ w hw hw0 η hη⟩
  -- the rotated rescalings along the subsequence
  have hvL : ∀ j, LocallyLipschitz
      (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) := fun j ↦
    locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz _ _ _
  have hiE : ∀ j, ∀ K : Set (Space (m + 1)), IsCompact K → IntegrableOn
      (rescaledPhaseEnergyDensity f (R (φ j))
        (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z))) K :=
    fun j K hK ↦ h.integrableOn_rescaledPhaseEnergy (hvL j)
      (fun z ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩) _ hK
  have hmodica := fun j ↦ hr.rescaled_isometry_modica_bound h (x (φ j)) (hR (φ j)) (Q (φ j))
  have hE0 : ∀ j z, 0 ≤ rescaledPhaseEnergyDensity f (R (φ j))
      (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) z := fun j z ↦ by
    have h1 := hr.rescaled_isometry_energy_sub_vertical_sq_nonneg h (x (φ j)) (hR (φ j))
      (Q (φ j)) z
    have h2 : 0 ≤ (R (φ j))⁻¹ * verticalDerivative
        (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) z ^ 2 :=
      mul_nonneg (inv_nonneg.mpr (hR (φ j)).le) (sq_nonneg _)
    linarith
  -- the cutoffs
  let bφ : ContDiffBump (0 : Space m) := ⟨1 / 4, 3 / 8, by norm_num, by norm_num⟩
  let bψ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 3 / 8, by norm_num, by norm_num⟩
  have hφ1 : ContDiff ℝ 1 (⇑bφ) := bφ.contDiff
  have hψ1 : ContDiff ℝ 1 (⇑bψ) := bψ.contDiff
  have hcφ : HasCompactSupport (⇑bφ) := bφ.hasCompactSupport
  have hcψ : HasCompactSupport (⇑bψ) := bψ.hasCompactSupport
  have htsφ : tsupport (⇑bφ) = closedBall 0 (3 / 8) := bφ.tsupport_eq
  have htsψ : tsupport (⇑bψ) = closedBall 0 (3 / 8) := bψ.tsupport_eq
  have hφU : tsupport (⇑bφ) ⊆ U := by
    rw [htsφ]
    exact (closedBall_subset_closedBall (by norm_num)).trans hBU
  have hφsq : ∀ y, bφ y ^ 2 ≤ 1 := fun y ↦ pow_le_one₀ bφ.nonneg bφ.le_one
  have hψsq : ∀ t, bψ t ^ 2 ≤ 1 := fun t ↦ pow_le_one₀ bψ.nonneg bψ.le_one
  have hφzero : ∀ y : Space m, 3 / 8 ≤ ‖y‖ → bφ y = 0 := fun y hy ↦
    Function.notMem_support.mp (by
      rw [bφ.support_eq, mem_ball, dist_zero_right]
      exact not_lt.mpr hy)
  have hψzero : ∀ t : ℝ, 3 / 8 ≤ |t| → bψ t = 0 := fun t ht ↦
    Function.notMem_support.mp (by
      rw [bψ.support_eq, mem_ball, dist_zero_right, Real.norm_eq_abs]
      exact not_lt.mpr ht)
  have hφone : ∀ y : Space m, ‖y‖ < 1 / 4 → bφ y = 1 := fun y hy ↦
    bφ.one_of_mem_closedBall (by
      rw [mem_closedBall, dist_zero_right]
      exact hy.le)
  have hψone : ∀ t : ℝ, |t| < 1 / 4 → bψ t = 1 := fun t ht ↦
    bψ.one_of_mem_closedBall (by
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      exact ht.le)
  have hψ0 : bψ 0 = 1 := hψone 0 (by norm_num)
  have hdψ : ∀ t : ℝ, |t| < 1 / 4 → deriv (⇑bψ) t = 0 := fun t ht ↦ by
    have hev : (⇑bψ) =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
      have hmem : t ∈ ball (0 : ℝ) (1 / 4) := by
        rw [mem_ball, dist_zero_right, Real.norm_eq_abs]
        exact ht
      filter_upwards [isOpen_ball.mem_nhds hmem] with s hs
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
      exact hψone s hs
    rw [hev.deriv_eq, deriv_const]
  have hgφr : ∀ y : Space m, 1 / 2 ≤ ‖y‖ → gradient (⇑bφ) y = 0 := fun y hy ↦
    ha6_gradient_eq_zero_of_notMem_tsupport (by
      rw [htsφ, mem_closedBall, dist_zero_right]
      linarith)
  have hφr : ∀ y : Space m, 1 / 2 ≤ ‖y‖ → bφ y = 0 := fun y hy ↦ hφzero y (by linarith)
  have hψr : ∀ t : ℝ, 1 / 2 ≤ |t| → bψ t = 0 := fun t ht ↦ hψzero t (by linarith)
  obtain ⟨Cg, hCg⟩ := (ha6_continuous_gradient hφ1).bounded_above_of_compact_support
    (ha6_hasCompactSupport_gradient hcφ)
  have hCg2 : ∀ y, ‖gradient (⇑bφ) y‖ ^ 2 ≤ Cg ^ 2 := fun y ↦
    pow_le_pow_left₀ (norm_nonneg _) (hCg y) 2
  have hdψc : Continuous (deriv (⇑bψ)) := hψ1.continuous_deriv le_rfl
  obtain ⟨Cψ, hCψ⟩ := (bψ.continuous.mul hdψc).bounded_above_of_compact_support
    (ha6_hasCompactSupport_of_zero hcψ fun t h0 ↦ by simp [h0])
  have hCψ' : ∀ t, |bψ t * deriv (⇑bψ) t| ≤ Cψ := fun t ↦ by
    have := hCψ t
    rwa [Real.norm_eq_abs] at this
  have hψ2s : tsupport (fun t ↦ bψ t ^ 2) ⊆ Ioo (-(1 / 2)) (1 / 2) := by
    refine (ha6_tsupport_subset_of_zero (G := fun t ↦ bψ t ^ 2) (φ := ⇑bψ)
      fun t h0 ↦ by simp [h0]).trans ?_
    rw [htsψ]
    intro t ht
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have hζs : ∀ ζ : Space m → Space m, (∀ y, bφ y = 0 → ζ y = 0) →
      tsupport ζ ⊆ ball (0 : Space m) (1 / 2) := fun ζ hζ ↦ by
    have hsub : tsupport ζ ⊆ tsupport (⇑bφ) :=
      closure_minimal (fun y (hy : y ∈ Function.support ζ) ↦
        subset_tsupport _ (fun h0 ↦ (Function.mem_support.mp hy) (hζ y h0)))
        (isClosed_tsupport _)
    refine hsub.trans ?_
    rw [htsφ]
    exact closedBall_subset_ball (by norm_num)
  have hgH : Continuous (gradient H) := ha6_continuous_gradient (hH.of_le (by norm_num))
  -- the HA6 limits
  have hKin : ∀ᶠ j in atTop, (∫ z, ha6Kin (R (φ j)) (δ (φ j))
      (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) bφ bψ z) ≤ 2 ^ m := by
    refine Eventually.of_forall fun j ↦ ?_
    refine (integral_ha6Kin_le_cylinderTilt (hR (φ j)) (hvL j) hφsq hψsq
      (fun y hy ↦ hφzero y (by linarith)) (fun t ht ↦ hψzero t (by linarith))).trans_eq ?_
    rw [htilt (φ j)]
    have := (hδ (φ j)).ne'
    field_simp
  have hHei : Tendsto (fun j ↦ ∫ z, ha6Height (R (φ j)) (δ (φ j)) (a j)
      (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) H bφ bψ z) atTop (𝓝 0) := by
    have hlim := hI1.const_mul (Cg ^ 2)
    rw [mul_zero] at hlim
    refine squeeze_zero (fun j ↦ integral_nonneg fun z ↦ ?_) (fun j ↦
      integral_ha6Height_le_cylinder (hR (φ j)) (hvL j) hH.continuous hψsq hCg2 hgφr hψr) hlim
    have := hR (φ j)
    unfold ha6Height
    positivity
  have hF1 := hI2 (fun y ↦ (bφ y * H y) • gradient (⇑bφ) y)
    ((bφ.continuous.mul hH.continuous).smul (ha6_continuous_gradient hφ1))
    (hζs _ fun y h0 ↦ by simp [h0]) (fun t ↦ bψ t ^ 2) (bψ.continuous.pow 2) hψ2s
  have hF2 := hI2 (fun y ↦ bφ y ^ 2 • gradient H y) ((bφ.continuous.pow 2).smul hgH)
    (hζs _ fun y h0 ↦ by simp [h0]) (fun t ↦ bψ t ^ 2) (bψ.continuous.pow 2) hψ2s
  have hTail : Tendsto (fun j ↦ ∫ z, ha6Tail f (R (φ j)) (δ (φ j)) (a j)
      (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) bφ bψ z) atTop (𝓝 0) := by
    have hlim := ((tendsto_const_nhds (x := (1 / 2 : ℝ)).add ha0.abs).const_mul Cψ).mul
      (hI3 (1 / 4) (by norm_num))
    rw [mul_zero] at hlim
    refine squeeze_zero (fun j ↦ integral_nonneg fun z ↦ ?_) (fun j ↦
      integral_ha6Tail_le_cylinder (hE0 j) (hiE j) hφsq hCψ' hφr hψr hdψ) hlim
    have := hE0 j z
    unfold ha6Tail
    positivity
  have hNor : ∀ η > 0, ∀ᶠ j in atTop, (∫ z, ha6Normal (R (φ j))
      (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z))
        (fun y ↦ bφ y ^ 2 * ‖gradient H y‖ ^ 2) bψ z) ≤
      σ * bψ 0 ^ 2 * (∫ y, bφ y ^ 2 * ‖gradient H y‖ ^ 2) + η := by
    intro η hη
    have hw : Continuous (fun y ↦ bφ y ^ 2 * ‖gradient H y‖ ^ 2) :=
      (bφ.continuous.pow 2).mul (hgH.norm.pow 2)
    have hw0 : ∀ y, 0 ≤ bφ y ^ 2 * ‖gradient H y‖ ^ 2 := fun y ↦ by positivity
    have hwr : ∀ y : Space m, 1 / 2 ≤ ‖y‖ → bφ y ^ 2 * ‖gradient H y‖ ^ 2 = 0 := fun y hy ↦ by
      rw [hφr y hy]
      ring
    have hball : (∫ y in ball (0 : Space m) (1 / 2), bφ y ^ 2 * ‖gradient H y‖ ^ 2) =
        ∫ y, bφ y ^ 2 * ‖gradient H y‖ ^ 2 := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ hwr y ?_
      rw [mem_ball, dist_zero_right, not_lt] at hy
      exact hy
    filter_upwards [hI4 (1 / 2) ⟨by norm_num, le_rfl⟩ _ hw hw0 η hη] with j hj
    refine (integral_ha6Normal_le_cylinder (hR (φ j)) (hvL j) hw hw0 hψsq hwr hψr).trans ?_
    rw [hψ0, one_pow, mul_one, ← hball]
    exact hj
  have hsq := tendsto_integral_ha6Square_of_limits (f := f) (a := a)
    (fun j ↦ hR (φ j)) (fun j ↦ hδ (φ j)) (fun j z ↦ h.zeroExtension_nonneg _) hvL hmodica hiE
    (fun j X hX hcX ↦ hr.rescaled_isometry_stress_stationarity h _ (hR (φ j)) _ _ hX hcX)
    hU hH hΔ hφ1 hcφ hφU hψ1 hcψ (σ := σ) (c := bψ 0 ^ 2) hKin hHei hF1 hF2 hTail hNor
  refine squeeze_zero (fun j ↦ setIntegral_nonneg (isOpen_tiltCylinder _ _).measurableSet
    fun z _ ↦ div_nonneg (sq_nonneg _) (hR (φ j)).le) (fun j ↦ ?_) hsq
  exact setIntegral_cylinder_le_integral_ha6Square (hR (φ j)) (hvL j) (hH.of_le (by norm_num))
    bφ.continuous hcφ bψ.continuous hcψ hφone hψone

/-- **HA0 from the HA6 inputs.** With `σ, M ≥ 0`, the HA6 inputs along HA11 contradiction
sequences give the HA0 cylinder tilt decay (HA6, then HA7 and HA11 of `DiffuseTiltDecay`). -/
theorem RigidityHypotheses.hasCylinderTiltDecay_of_heightData {f : ℝ → ℝ} {κ : ℝ}
    {g : Space m → ℝ} {u : Space (m + 1) → ℝ} (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {σ M : ℝ} (hσ : 0 ≤ σ) (hM : 0 ≤ M)
    (hdata : HasHarmonicHeightData g u f σ M) : HasCylinderTiltDecay g u :=
  h.hasCylinderTiltDecay_of_harmonicApproximation hσ hM
    (hr.hasHarmonicApproximation_of_heightData h hdata)

end SerrinEpigraph
