module

public import SerrinEpigraph.LayerProfile
public import SerrinEpigraph.PhysicalTranslationStress
public import SerrinEpigraph.PhysicalTranslationEquation
public import SerrinEpigraph.PhysicalTranslationEnergyLimit
public import SerrinEpigraph.BoundaryWeakInequality
public import SerrinEpigraph.BVColumnGraph
public import SerrinEpigraph.HarmonicHeightEstimates
public import SerrinEpigraph.DirectionalInvariance
public import SerrinEpigraph.PlaneTiltRotation
public import SerrinEpigraph.EuclideanProductVolume
public import SerrinEpigraph.PlaneTiltTranslatedClearing

/-!
# One-dimensional microscopic limits are layer profiles (HA9.a)

Let `V` be a locally uniform limit of physical translates `x ↦ U(p_j + x)` of the zero extension
`U`, depending only on the coordinate along a unit vector `e`, and let `P τ = V (τ • e)`. This file
proves `RigidityHypotheses.isHamiltonianProfile_of_oneDimensional_limit`: under an all-center
surface energy bound `∫_{B_r(z)} e(U) ≤ L r^m`, `P` is an `IsHamiltonianProfile`, so the
classification of `SerrinEpigraph.LayerProfile` applies. The steps are:

* the limit equation (`physical_translation_limit_distributional_equation`) tested with
  `η(π Q⁻¹ x) ζ(⟪e, x⟫)` gives the one-dimensional weak equation `∫ P' ζ' = ∫ f(P) ζ` on `{P > 0}`;
* the limit stress identity (`physical_translation_limit_stress_stationarity`) tested with
  `η(π Q⁻¹ x) ζ(⟪e, x⟫) e` gives `∫ h ζ' = 0` for the one-dimensional Hamiltonian
  `h = 1_{P > 0} (P'²/2 + W(P)) - P'²`, so `h` is a.e. constant (du Bois-Reymond);
* the energy bound passes to `V` and forces the constant to vanish (`|h| ≤ e(V)` pointwise and a
  nonzero constant would give energy of volume order `r^{m+1}`);
* the weak equation and du Bois-Reymond give `P ∈ C¹` on `{P > 0}`, hence `P'² = 2 W(P)` there.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff

namespace SerrinEpigraph

variable {m : ℕ}

/-! ### Coordinates along a unit vector -/

/-- In coordinates `x = Q z` with `Q eₙ = e`, the coordinate along `e` is the last coordinate. -/
theorem inner_eq_last_symm {e : Space (m + 1)} (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (hQ : Q (verticalDirection m) = e) (x : Space (m + 1)) :
    inner ℝ e x = (Q.symm x) (Fin.last m) := by
  calc inner ℝ e x = inner ℝ (Q (verticalDirection m)) (Q (Q.symm x)) := by
        rw [hQ, LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℝ (verticalDirection m) (Q.symm x) := Q.inner_map_map _ _
    _ = (Q.symm x) (Fin.last m) := by rw [real_inner_comm, inner_verticalDirection_right]

/-- An almost-everywhere property of the coordinate along `e` holds almost everywhere. -/
theorem ae_inner_of_ae {e : Space (m + 1)} (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (hQ : Q (verticalDirection m) = e) {p : ℝ → Prop} (hp : ∀ᵐ τ, p τ) :
    ∀ᵐ x : Space (m + 1), p (inner ℝ e x) := by
  have h1 : ∀ᵐ q ∂((volume : Measure (Space m)).prod volume), p q.2 :=
    Measure.quasiMeasurePreserving_snd.ae hp
  have h2 : ∀ᵐ z : Space (m + 1), p (z (Fin.last m)) :=
    (measurePreserving_horizontal_last m).quasiMeasurePreserving.ae h1
  have h3 : ∀ᵐ x : Space (m + 1), p ((Q.symm x) (Fin.last m)) :=
    Q.symm.measurePreserving.quasiMeasurePreserving.ae h2
  filter_upwards [h3] with x hx
  rwa [inner_eq_last_symm Q hQ x]

private theorem horizontal_verticalDirection_eq_zero : horizontal (verticalDirection m) = 0 := by
  ext i
  simp [horizontal, verticalDirection, Fin.castSucc_ne_last]

/-- **Fubini along `e`.** -/
theorem integral_inner_mul_horizontal_symm {e : Space (m + 1)}
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (hQ : Q (verticalDirection m) = e) {H : ℝ → ℝ}
    (hH : Integrable H) {η : Space m → ℝ} (hη : Integrable η) :
    ∫ x, H (inner ℝ e x) * η (horizontal (Q.symm x)) = (∫ τ, H τ) * ∫ y, η y := by
  have hcv := Q.measurePreserving.integral_comp Q.toHomeomorph.measurableEmbedding
    (fun x ↦ H (inner ℝ e x) * η (horizontal (Q.symm x)))
  rw [← hcv]
  have hpt : ∀ z, H (inner ℝ e (Q z)) * η (horizontal (Q.symm (Q z))) =
      η (horizontal z) * H (z (Fin.last m)) := by
    intro z
    rw [inner_eq_last_symm Q hQ, LinearIsometryEquiv.symm_apply_apply, mul_comm]
  simp_rw [hpt]
  have hprod : Integrable (fun q : Space m × ℝ ↦ η q.1 * H q.2)
      ((volume : Measure (Space m)).prod volume) := hη.mul_prod hH
  have hint : Integrable (fun z : Space (m + 1) ↦ η (horizontal z) * H (z (Fin.last m))) := by
    have := ((measurePreserving_horizontal_last m).integrable_comp
      hprod.aestronglyMeasurable).mpr hprod
    exact this
  rw [integral_space_eq_integral_horizontal_vertical hint]
  simp only [horizontal_point, last_point]
  simp_rw [integral_const_mul]
  rw [integral_mul_const, mul_comm]

/-! ### One-dimensional limits -/

variable {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The gradient of a one-dimensional function `V = P(⟪e, ·⟫)`. -/
theorem gradient_eq_deriv_smul_of_oneDimensional {d : ℕ} {V : Space d → ℝ} {e : Space d}
    (h1D : ∀ x, V x = V ((inner ℝ e x) • e)) {x : Space d}
    (hd : DifferentiableAt ℝ (fun τ ↦ V (τ • e)) (inner ℝ e x)) :
    gradient V x = deriv (fun τ ↦ V (τ • e)) (inner ℝ e x) • e := by
  have hl : HasFDerivAt (fun z : Space d ↦ inner ℝ e z)
      (toDual ℝ (Space d) e : StrongDual ℝ (Space d)) x := by
    have h1 := (toDual ℝ (Space d) e : StrongDual ℝ (Space d)).hasFDerivAt (x := x)
    have hfeq : (⇑(toDual ℝ (Space d) e : StrongDual ℝ (Space d)) : Space d → ℝ) =
        fun z ↦ inner ℝ e z := funext fun z ↦ by simp
    rwa [hfeq] at h1
  have hc := hd.hasDerivAt.comp_hasFDerivAt x hl
  have hV' : HasFDerivAt V (deriv (fun τ ↦ V (τ • e)) (inner ℝ e x) •
      (toDual ℝ (Space d) e : StrongDual ℝ (Space d))) x :=
    hc.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ h1D z)
  simp only [gradient]
  rw [hV'.fderiv, map_smul, LinearIsometryEquiv.symm_apply_apply]

/-- The energy bound passes to physical translation limits. -/
theorem RigidityHypotheses.physical_limit_energy_le (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    {p : ℕ → Space (m + 1)} {V : Space (m + 1) → ℝ}
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (z : Space (m + 1)) {r : ℝ} (hr0 : 0 < r) :
    (∫ x in closedBall z r, phaseEnergyDensity f 0 V x) ≤ L * r ^ m := by
  have hK := isCompact_closedBall z r
  have ht := hr.physical_translation_energy_tendsto h hV hval hlim hK
  have hU (j : ℕ) : LocallyLipschitz (fun x ↦ zeroExtension g u (p j + x)) :=
    h.zeroExtension_locallyLipschitz.comp (isometry_add_left (p j)).lipschitzWith.locallyLipschitz
  have hUv (j : ℕ) (x : Space (m + 1)) : zeroExtension g u (p j + x) ∈ Icc 0 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hiV := h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hval 0 hK
  have hbd : ∀ j, (∫ x in closedBall z r, phaseEnergyDensity f 0 V x) ≤
      L * r ^ m + ∫ x in closedBall z r,
        ‖phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (p j + y)) x -
          phaseEnergyDensity f 0 V x‖ := by
    intro j
    have hij := h.integrableOn_lipschitz_phaseEnergy (hU j) (hUv j) 0 hK
    have hdiff : IntegrableOn (fun x ↦ ‖phaseEnergyDensity f 0
        (fun y ↦ zeroExtension g u (p j + y)) x - phaseEnergyDensity f 0 V x‖)
        (closedBall z r) := (hij.sub hiV).norm
    have hle : (∫ x in closedBall z r, phaseEnergyDensity f 0 V x) ≤
        (∫ x in closedBall z r, phaseEnergyDensity f 0
          (fun y ↦ zeroExtension g u (p j + y)) x) +
        ∫ x in closedBall z r, ‖phaseEnergyDensity f 0
          (fun y ↦ zeroExtension g u (p j + y)) x - phaseEnergyDensity f 0 V x‖ := by
      rw [← integral_add hij hdiff]
      refine integral_mono hiV (hij.add hdiff) (fun x ↦ ?_)
      have h1 := le_abs_self (phaseEnergyDensity f 0 V x -
        phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (p j + y)) x)
      rw [abs_sub_comm, ← Real.norm_eq_abs] at h1
      change phaseEnergyDensity f 0 V x ≤
        phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (p j + y)) x +
          ‖phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (p j + y)) x -
            phaseEnergyDensity f 0 V x‖
      linarith
    have htrans : (∫ x in closedBall z r, phaseEnergyDensity f 0
        (fun y ↦ zeroExtension g u (p j + y)) x) ≤ L * r ^ m := by
      simp_rw [phaseEnergyDensity_comp_add_left]
      rw [setIntegral_closedBall_comp_add_left_center
        (fun y ↦ phaseEnergyDensity f 0 (zeroExtension g u) y) (p j) z r]
      exact hbound _ r hr0
    linarith
  have hlimit : Tendsto (fun j ↦ L * r ^ m + ∫ x in closedBall z r,
      ‖phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (p j + y)) x -
        phaseEnergyDensity f 0 V x‖) atTop (𝓝 (L * r ^ m)) := by
    simpa using ht.const_add (L * r ^ m)
  exact ge_of_tendsto' hlimit hbd

/-- A normalized smooth bump on the horizontal space. -/
private theorem exists_horizontal_bump :
    ∃ η : Space m → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ ∫ y, η y = 1 := by
  let η : ContDiffBump (0 : Space m) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨η.normed volume, η.contDiff_normed, η.hasCompactSupport_normed, η.integral_normed⟩

/-- The rotated product test `x ↦ η(π Q⁻¹ x) ζ(⟪e, x⟫)` and its derivative along `e`. -/
private theorem rotatedTest_props {e : Space (m + 1)} (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (hQ : Q (verticalDirection m) = e) {η : Space m → ℝ} {ζ : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ η (horizontal (Q.symm x)) * ζ (inner ℝ e x)) ∧
      HasCompactSupport (fun x ↦ η (horizontal (Q.symm x)) * ζ (inner ℝ e x)) ∧
      tsupport (fun x ↦ η (horizontal (Q.symm x)) * ζ (inner ℝ e x)) ⊆
        {x | inner ℝ e x ∈ tsupport ζ} ∧
      ∀ x, fderiv ℝ (fun x ↦ η (horizontal (Q.symm x)) * ζ (inner ℝ e x)) x e =
        η (horizontal (Q.symm x)) * deriv ζ (inner ℝ e x) := by
  have hfun : (fun x ↦ η (horizontal (Q.symm x)) * ζ (inner ℝ e x)) =
      (fun z : Space (m + 1) ↦ η (horizontal z) * ζ (z (Fin.last m))) ∘ Q.symm := by
    funext x
    simp only [Function.comp_apply, inner_eq_last_symm Q hQ x]
  have hphi0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Space (m + 1) ↦ η (horizontal z) * ζ (z (Fin.last m))) :=
    (hη.comp horizontalContinuousLinearMap.contDiff).mul
      (hζ.comp (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).contDiff)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hphi0.comp Q.symm.contDiff
  · -- compact support: inside `Q (point '' (tsupport η ×ˢ tsupport ζ))`
    have hK : IsCompact (Q '' ((fun q : Space m × ℝ ↦ point q.1 q.2) '' (tsupport η ×ˢ
        tsupport ζ))) :=
      ((hηc.prod hζc).image pointContinuousLinearMap.continuous).image Q.continuous
    refine HasCompactSupport.intro hK (fun x hx ↦ ?_)
    by_contra hne
    apply hx
    have h1 : η (horizontal (Q.symm x)) ≠ 0 := left_ne_zero_of_mul hne
    have h2 : ζ (inner ℝ e x) ≠ 0 := right_ne_zero_of_mul hne
    refine ⟨Q.symm x, ⟨(horizontal (Q.symm x), (Q.symm x) (Fin.last m)),
      ⟨subset_tsupport _ h1, ?_⟩, by simp⟩, by simp⟩
    rw [← inner_eq_last_symm Q hQ x]
    exact subset_tsupport _ h2
  · apply closure_minimal _ ((isClosed_tsupport ζ).preimage (continuous_const.inner continuous_id))
    intro x hx
    exact subset_tsupport _ (right_ne_zero_of_mul hx)
  · intro x
    have hd : HasFDerivAt (fun x ↦ Q.symm x)
        (Q.symm.toContinuousLinearEquiv : Space (m + 1) →L[ℝ] Space (m + 1)) x :=
      Q.symm.toContinuousLinearEquiv.hasFDerivAt
    rw [hfun, ((hphi0.differentiable (by simp) (Q.symm x)).hasFDerivAt.comp x hd).fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [fderiv_horizontal_mul_last_apply (hη.differentiable (by simp))
      (hζ.differentiable (by simp))]
    have hQe : Q.symm e = verticalDirection m := by
      rw [← hQ, LinearIsometryEquiv.symm_apply_apply]
    rw [hQe, horizontal_verticalDirection_eq_zero, map_zero, mul_zero, add_zero,
      ← inner_eq_last_symm Q hQ x]
    simp [verticalDirection]

/-- **The one-dimensional weak equation.** -/
theorem RigidityHypotheses.oneDimensional_limit_weak_equation (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : ℕ → Space (m + 1)} {V : Space (m + 1) → ℝ}
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (h1D : ∀ x, V x = V ((inner ℝ e x) • e))
    {ζ : ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (hζs : tsupport ζ ⊆ {τ | 0 < V (τ • e)}) :
    ∫ τ, deriv (fun τ ↦ V (τ • e)) τ * deriv ζ τ = ∫ τ, f (V (τ • e)) * ζ τ := by
  set P : ℝ → ℝ := fun τ ↦ V (τ • e) with hPdef
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_vertical he
  obtain ⟨η, hη, hηc, hη1⟩ := exists_horizontal_bump (m := m)
  obtain ⟨hφs, hφc, hφsupp, hφd⟩ := rotatedTest_props Q hQ hη hηc hζ hζc
  set φ : Space (m + 1) → ℝ := fun x ↦ η (horizontal (Q.symm x)) * ζ (inner ℝ e x) with hφdef
  have hVP : ∀ x, V x = P (inner ℝ e x) := h1D
  have hφpos : tsupport φ ⊆ {x | 0 < V x} := by
    intro x hx
    have := hζs (hφsupp hx)
    simp only [mem_ofPred_eq] at this ⊢
    rwa [hVP x]
  have heq := hr.physical_translation_limit_distributional_equation h hV.continuous hval hlim
    (hφs.of_le (by simp)) hφc hφpos
  have hibp := integral_mul_laplacian_eq_neg_inner_gradient_of_locallyLipschitz
    hV.locallyLipschitz (B := 1) hval (hφs.of_le (by simp)) hφc
  have hmain : ∫ x, inner ℝ (gradient V x) (gradient φ x) = ∫ x, f (V x) * φ x := by linarith
  -- `P` is Lipschitz, hence differentiable almost everywhere
  have hPlip : LipschitzWith ⟨κ, h.kappa_pos.le⟩ P := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have h1 := hV.dist_le_mul (a • e) (b • e)
    have h2 : dist (a • e) (b • e) = dist a b := by
      rw [dist_eq_norm, ← sub_smul, norm_smul, he, mul_one, Real.dist_eq, Real.norm_eq_abs]
    rw [h2] at h1
    exact h1
  have hdiff : ∀ᵐ τ, DifferentiableAt ℝ P τ := hPlip.ae_differentiableAt
  have hdiffx := ae_inner_of_ae Q hQ hdiff
  have hpt : ∀ᵐ x, inner ℝ (gradient V x) (gradient φ x) =
      (deriv P (inner ℝ e x) * deriv ζ (inner ℝ e x)) * η (horizontal (Q.symm x)) := by
    filter_upwards [hdiffx] with x hx
    rw [gradient_eq_deriv_smul_of_oneDimensional h1D hx, real_inner_smul_left,
      real_inner_comm (gradient φ x) e, inner_gradient_left, hφd x]
    ring
  have hfpt : ∀ x, f (V x) * φ x = (f (P (inner ℝ e x)) * ζ (inner ℝ e x)) *
      η (horizontal (Q.symm x)) := by
    intro x
    rw [hVP x, hφdef]
    ring
  -- integrability of the one-dimensional integrands
  have hPd_bound : ∀ τ, ‖deriv P τ‖ ≤ κ := fun τ ↦ norm_deriv_le_of_lipschitz hPlip
  have hζ'c : Continuous (deriv ζ) := hζ.continuous_deriv (by simp)
  have hζ'cs : HasCompactSupport (deriv ζ) := hζc.deriv
  have hH1 : Integrable (fun τ ↦ deriv P τ * deriv ζ τ) := by
    have hi := (hζ'c.integrable_of_hasCompactSupport (μ := volume) hζ'cs).mul_bdd
      (measurable_deriv P).aestronglyMeasurable (Eventually.of_forall hPd_bound)
    simpa only [mul_comm] using hi
  have hfP : Continuous (fun τ ↦ f (P τ)) :=
    h.reaction_contDiffOn.continuousOn.comp_continuous hPlip.continuous
      (fun τ ↦ (hval _).1)
  have hH2 : Integrable (fun τ ↦ f (P τ) * ζ τ) :=
    (hfP.mul hζ.continuous).integrable_of_hasCompactSupport hζc.mul_left
  have hηi : Integrable η := hη.continuous.integrable_of_hasCompactSupport hηc
  rw [integral_congr_ae hpt, integral_inner_mul_horizontal_symm Q hQ hH1 hηi, hη1, mul_one]
    at hmain
  simp_rw [hfpt] at hmain
  rw [integral_inner_mul_horizontal_symm Q hQ hH2 hηi, hη1, mul_one] at hmain
  exact hmain

/-- The one-dimensional Hamiltonian `1_{P > 0} (P'²/2 + W(P)) - P'²` of a profile. -/
def layerHamiltonian (f : ℝ → ℝ) (P : ℝ → ℝ) (τ : ℝ) : ℝ :=
  {σ | 0 < P σ}.indicator (fun σ ↦ deriv P σ ^ 2 / 2 + normalizedPotential f (P σ)) τ -
    deriv P τ ^ 2

/-- The profile of a one-dimensional `κ`-Lipschitz function is `κ`-Lipschitz. -/
private theorem lipschitzWith_profile {d : ℕ} {V : Space d → ℝ} {e : Space d} {K : NNReal}
    (hV : LipschitzWith K V) (he : ‖e‖ = 1) : LipschitzWith K (fun τ : ℝ ↦ V (τ • e)) := by
  apply LipschitzWith.of_dist_le_mul
  intro a c
  have h1 := hV.dist_le_mul (a • e) (c • e)
  have h2 : dist (a • e) (c • e) = dist a c := by
    rw [dist_eq_norm, ← sub_smul, norm_smul, he, mul_one, Real.dist_eq, Real.norm_eq_abs]
  rw [h2] at h1
  exact h1

/-- Measurability and a uniform bound for the Hamiltonian of a Lipschitz profile. -/
private theorem layerHamiltonian_measurable_bound (h : Hypotheses g u f κ) {P : ℝ → ℝ}
    (hPlip : LipschitzWith ⟨κ, h.kappa_pos.le⟩ P) (hPval : ∀ τ, P τ ∈ Icc (0 : ℝ) 1) :
    Measurable (layerHamiltonian f P) ∧ ∃ C : ℝ, ∀ τ, ‖layerHamiltonian f P τ‖ ≤ C := by
  obtain ⟨Wm, hWm⟩ := isCompact_Icc.exists_bound_of_continuousOn h.normalizedPotential_continuousOn
  have hWc : Continuous (fun σ ↦ normalizedPotential f (P σ)) :=
    h.normalizedPotential_continuousOn.comp_continuous hPlip.continuous hPval
  have hdm : Measurable (deriv P) := measurable_deriv P
  have hdb : ∀ τ, |deriv P τ| ≤ κ := fun τ ↦ by
    have := norm_deriv_le_of_lipschitz (x₀ := τ) hPlip
    rw [Real.norm_eq_abs] at this
    exact this
  have hmeas : Measurable (layerHamiltonian f P) := by
    have h1 : Measurable (fun σ ↦ deriv P σ ^ 2 / 2 + normalizedPotential f (P σ)) :=
      ((hdm.pow_const 2).div_const 2).add hWc.measurable
    have h2 : Measurable ({σ | 0 < P σ}.indicator
        (fun σ ↦ deriv P σ ^ 2 / 2 + normalizedPotential f (P σ))) :=
      h1.indicator (measurableSet_lt (measurable_const (a := (0 : ℝ)))
        hPlip.continuous.measurable)
    exact h2.sub (hdm.pow_const 2)
  refine ⟨hmeas, κ ^ 2 / 2 + |Wm| + κ ^ 2, fun τ ↦ ?_⟩
  have hd2 : deriv P τ ^ 2 ≤ κ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hdb τ) 2
  have hW : |normalizedPotential f (P τ)| ≤ |Wm| := by
    have := hWm (P τ) (hPval τ)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hind : |{σ | 0 < P σ}.indicator
      (fun σ ↦ deriv P σ ^ 2 / 2 + normalizedPotential f (P σ)) τ| ≤ κ ^ 2 / 2 + |Wm| := by
    by_cases hτ : τ ∈ {σ | 0 < P σ}
    · rw [indicator_of_mem hτ]
      calc |deriv P τ ^ 2 / 2 + normalizedPotential f (P τ)|
          ≤ |deriv P τ ^ 2 / 2| + |normalizedPotential f (P τ)| := abs_add_le _ _
        _ ≤ κ ^ 2 / 2 + |Wm| := by
            rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ deriv P τ ^ 2 / 2)]
            linarith
    · rw [indicator_of_notMem hτ, abs_zero]
      positivity
  rw [Real.norm_eq_abs, layerHamiltonian]
  calc _ ≤ |{σ | 0 < P σ}.indicator
        (fun σ ↦ deriv P σ ^ 2 / 2 + normalizedPotential f (P σ)) τ| + |deriv P τ ^ 2| :=
        abs_sub _ _
    _ ≤ κ ^ 2 / 2 + |Wm| + κ ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg (deriv P τ))]
        linarith

/-- **The one-dimensional stress identity.** -/
theorem RigidityHypotheses.oneDimensional_limit_stress (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : ℕ → Space (m + 1)} {V : Space (m + 1) → ℝ}
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (h1D : ∀ x, V x = V ((inner ℝ e x) • e))
    {ζ : ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) :
    ∫ τ, layerHamiltonian f (fun τ ↦ V (τ • e)) τ * deriv ζ τ = 0 := by
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_vertical he
  obtain ⟨η, hη, hηc, hη1⟩ := exists_horizontal_bump (m := m)
  obtain ⟨hφs, hφc, -, hφd⟩ := rotatedTest_props Q hQ hη hηc hζ hζc
  set φ : Space (m + 1) → ℝ := fun x ↦ η (horizontal (Q.symm x)) * ζ (inner ℝ e x) with hφdef
  have hφ1 : ContDiff ℝ 1 φ := hφs.of_le (by simp)
  have hX : ContDiff ℝ 1 (fun x ↦ φ x • e) := hφ1.smul contDiff_const
  have hXc : HasCompactSupport (fun x ↦ φ x • e) := hφc.smul_right
  have hstress := hr.physical_translation_limit_stress_stationarity h hV hval hlim
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) hX hXc
  have hPlip := lipschitzWith_profile hV he
  have hdiffx := ae_inner_of_ae Q hQ hPlip.ae_differentiableAt
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hpt : ∀ᵐ x, phaseEnergyDensity f 0 V x * fieldDivergence
      (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) (fun x ↦ φ x • e) x -
      inner ℝ (gradient V x) (fderiv ℝ (fun x ↦ φ x • e) x (gradient V x)) =
      (layerHamiltonian f (fun τ ↦ V (τ • e)) (inner ℝ e x) * deriv ζ (inner ℝ e x)) *
        η (horizontal (Q.symm x)) := by
    filter_upwards [hdiffx] with x hx
    have hφx : DifferentiableAt ℝ φ x := hφs.differentiable (by simp) x
    set P' := deriv (fun τ ↦ V (τ • e)) (inner ℝ e x) with hP'
    have hgrad := gradient_eq_deriv_smul_of_oneDimensional h1D hx
    have hterm : inner ℝ (P' • e) ((fderiv ℝ φ x (P' • e)) • e) = P' ^ 2 * fderiv ℝ φ x e := by
      rw [map_smul, smul_eq_mul, real_inner_smul_left, real_inner_smul_right, hee]
      ring
    rw [fieldDivergence_smul_const_eq_fderiv _ hφx, (hφx.hasFDerivAt.smul_const e).fderiv,
      ContinuousLinearMap.smulRight_apply, hgrad, hterm, hφd x]
    have hnorm : ‖P' • e‖ ^ 2 = P' ^ 2 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
    by_cases hpos : 0 < V (inner ℝ e x • e)
    · have hmem : x ∈ {y | 0 < V y} := by
        change 0 < V x
        rw [h1D x]
        exact hpos
      have hmem' : inner ℝ e x ∈ {σ | 0 < V (σ • e)} := hpos
      rw [phaseEnergyDensity, indicator_of_mem hmem, hgrad, hnorm, layerHamiltonian,
        indicator_of_mem hmem', h1D x, add_zero]
      ring
    · have hmem : x ∉ {y | 0 < V y} := by
        change ¬0 < V x
        rw [h1D x]
        exact hpos
      have hmem' : inner ℝ e x ∉ {σ | 0 < V (σ • e)} := hpos
      rw [phaseEnergyDensity, indicator_of_notMem hmem, layerHamiltonian,
        indicator_of_notMem hmem']
      ring
  rw [integral_congr_ae hpt] at hstress
  obtain ⟨hHm, C, hC⟩ := layerHamiltonian_measurable_bound h hPlip (fun τ ↦ hval _)
  have hζ'c : Continuous (deriv ζ) := hζ.continuous_deriv (by simp)
  have hH : Integrable (fun τ ↦ layerHamiltonian f (fun τ ↦ V (τ • e)) τ * deriv ζ τ) := by
    have hi := (hζ'c.integrable_of_hasCompactSupport (μ := volume) hζc.deriv).mul_bdd
      hHm.aestronglyMeasurable (Eventually.of_forall hC)
    simpa only [mul_comm] using hi
  have hηi : Integrable η := hη.continuous.integrable_of_hasCompactSupport hηc
  rw [integral_inner_mul_horizontal_symm Q hQ hH hηi, hη1, mul_one] at hstress
  exact hstress

/-- **The Hamiltonian vanishes.** Under an all-center surface energy bound, the one-dimensional
Hamiltonian of a one-dimensional physical limit vanishes almost everywhere. -/
theorem RigidityHypotheses.oneDimensional_limit_hamiltonian_ae_eq_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    {p : ℕ → Space (m + 1)} {V : Space (m + 1) → ℝ}
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (h1D : ∀ x, V x = V ((inner ℝ e x) • e)) :
    ∀ᵐ τ, layerHamiltonian f (fun τ ↦ V (τ • e)) τ = 0 := by
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_vertical he
  have hPlip := lipschitzWith_profile hV he
  have hPval : ∀ τ : ℝ, V (τ • e) ∈ Icc (0 : ℝ) 1 := fun τ ↦ hval _
  obtain ⟨hHm, C, hC⟩ := layerHamiltonian_measurable_bound h hPlip hPval
  have hloc : LocallyIntegrableOn (layerHamiltonian f (fun τ ↦ V (τ • e))) univ := by
    rw [locallyIntegrableOn_univ]
    refine (Continuous.locallyIntegrable (continuous_const (y := C))).mono hHm.aestronglyMeasurable
      (Eventually.of_forall fun τ ↦ ?_)
    rw [Real.norm_eq_abs C]
    exact (hC τ).trans (le_abs_self C)
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_mul_deriv_eq_zero isOpen_univ ordConnected_univ
    univ_nonempty hloc (fun ψ hψ hψc _ ↦ hr.oneDimensional_limit_stress h hV hval hlim he h1D
      hψ hψc)
  have hc' : ∀ᵐ τ, layerHamiltonian f (fun τ ↦ V (τ • e)) τ = c := by
    filter_upwards [hc] with τ hτ
    exact hτ (mem_univ τ)
  suffices hc0 : c = 0 by
    filter_upwards [hc'] with τ hτ
    rw [hτ, hc0]
  by_contra hc0
  -- the energy density dominates `|c|` almost everywhere
  have hdom : ∀ᵐ x : Space (m + 1), |c| ≤ phaseEnergyDensity f 0 V x := by
    have hboth : ∀ᵐ τ : ℝ, DifferentiableAt ℝ (fun τ : ℝ ↦ V (τ • e)) τ ∧
        layerHamiltonian f (fun τ : ℝ ↦ V (τ • e)) τ = c := by
      filter_upwards [hPlip.ae_differentiableAt, hc'] with τ h1 h2
      exact ⟨h1, h2⟩
    filter_upwards [ae_inner_of_ae Q hQ hboth] with x ⟨hx, hxc⟩
    set P' := deriv (fun τ ↦ V (τ • e)) (inner ℝ e x) with hP'
    have hgrad := gradient_eq_deriv_smul_of_oneDimensional h1D hx
    have hnorm : ‖P' • e‖ ^ 2 = P' ^ 2 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
    by_cases hpos : 0 < V (inner ℝ e x • e)
    · have hmem : x ∈ {y | 0 < V y} := by
        change 0 < V x
        rw [h1D x]
        exact hpos
      have hmem' : inner ℝ e x ∈ {σ | 0 < V (σ • e)} := hpos
      have hW := hr.normalizedPotential_nonneg h (hPval (inner ℝ e x))
      rw [phaseEnergyDensity, indicator_of_mem hmem, hgrad, hnorm, h1D x, add_zero]
      rw [← hxc, layerHamiltonian, indicator_of_mem hmem', abs_le]
      constructor <;> nlinarith [sq_nonneg P']
    · exfalso
      have hP0 : V (inner ℝ e x • e) = 0 := le_antisymm (not_lt.mp hpos) (hPval _).1
      have hmin : IsLocalMin (fun τ ↦ V (τ • e)) (inner ℝ e x) :=
        Eventually.of_forall fun σ ↦ by
          change V (inner ℝ e x • e) ≤ V (σ • e)
          rw [hP0]
          exact (hPval σ).1
      have hd0 : P' = 0 := hmin.deriv_eq_zero
      have hmem' : inner ℝ e x ∉ {σ | 0 < V (σ • e)} := hpos
      rw [layerHamiltonian, indicator_of_notMem hmem', ← hP', hd0] at hxc
      apply hc0
      rw [← hxc]
      ring
  -- the energy bound in large balls
  have hm1 : Module.finrank ℝ (Space (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  set vol₁ := volume.real (ball (0 : Space (m + 1)) 1) with hvol₁
  have hvol₁pos : 0 < vol₁ := by
    rw [hvol₁, Measure.real]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne'
      (measure_ball_lt_top (μ := volume)).ne
  have hcabs : 0 < |c| := abs_pos.mpr hc0
  set r : ℝ := (|L| + 1) / (|c| * vol₁) + 1 with hr_def
  have hr0 : 0 < r := by positivity
  have hupper := hr.physical_limit_energy_le h hbound hV hval hlim 0 hr0
  have hvol : volume.real (closedBall (0 : Space (m + 1)) r) = r ^ (m + 1) * vol₁ := by
    rw [Measure.real, Measure.addHaar_closedBall volume 0 hr0.le, hm1, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hvol₁, Measure.real]
  have hlower : |c| * (r ^ (m + 1) * vol₁) ≤
      ∫ x in closedBall (0 : Space (m + 1)) r, phaseEnergyDensity f 0 V x := by
    have hiV := h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hval 0
      (isCompact_closedBall (0 : Space (m + 1)) r)
    have hconst : IntegrableOn (fun _ : Space (m + 1) ↦ |c|) (closedBall 0 r) :=
      integrableOn_const (measure_closedBall_lt_top (μ := volume)).ne
    have := setIntegral_mono_ae hconst hiV hdom
    rwa [setIntegral_const, smul_eq_mul, hvol, mul_comm] at this
  have hkey : |c| * vol₁ * r ≤ L := by
    have hrm : 0 < r ^ m := pow_pos hr0 m
    have h1 : |c| * (r ^ (m + 1) * vol₁) ≤ L * r ^ m := hlower.trans hupper
    have h2 : |c| * (r ^ (m + 1) * vol₁) = (|c| * vol₁ * r) * r ^ m := by ring
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 hrm
  have hbig : |L| + 1 < |c| * vol₁ * r := by
    have hcw : 0 < |c| * vol₁ := mul_pos hcabs hvol₁pos
    have : |c| * vol₁ * ((|L| + 1) / (|c| * vol₁)) = |L| + 1 := by field_simp
    rw [hr_def, mul_add, this, mul_one]
    linarith
  linarith [le_abs_self L]

/-- Local regularity of a one-dimensional limit on its positive set: `P ∈ C¹` there. -/
theorem RigidityHypotheses.oneDimensional_limit_regular (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : ℕ → Space (m + 1)} {V : Space (m + 1) → ℝ}
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (h1D : ∀ x, V x = V ((inner ℝ e x) • e))
    {τ₀ : ℝ} (hτ₀ : 0 < V (τ₀ • e)) :
    HasDerivAt (fun τ ↦ V (τ • e)) (deriv (fun τ ↦ V (τ • e)) τ₀) τ₀ ∧
      ContinuousAt (deriv (fun τ ↦ V (τ • e))) τ₀ := by
  set P : ℝ → ℝ := fun τ ↦ V (τ • e) with hPdef
  have hPlip : LipschitzWith ⟨κ, h.kappa_pos.le⟩ P := lipschitzWith_profile hV he
  have hPval : ∀ τ, P τ ∈ Icc (0 : ℝ) 1 := fun τ ↦ hval _
  have hO : IsOpen {τ | 0 < P τ} := isOpen_lt continuous_const hPlip.continuous
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.mp hO τ₀ hτ₀
  set J := Metric.ball τ₀ δ with hJ
  have hJo : IsOpen J := Metric.isOpen_ball
  have hJc : J.OrdConnected := by rw [hJ, Real.ball_eq_Ioo]; exact ordConnected_Ioo
  have hfP : Continuous (fun τ ↦ f (P τ)) :=
    h.reaction_contDiffOn.continuousOn.comp_continuous hPlip.continuous (fun τ ↦ (hPval τ).1)
  set F : ℝ → ℝ := fun σ ↦ ∫ r in τ₀..σ, f (P r) with hFdef
  have hF : ∀ σ, HasDerivAt F (f (P σ)) σ := fun σ ↦
    (hfP.integral_hasStrictDerivAt τ₀ σ).hasDerivAt
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun σ ↦ (hF σ).continuousAt
  have hdb : ∀ σ, ‖deriv P σ‖ ≤ κ := fun σ ↦ by
    have := norm_deriv_le_of_lipschitz (x₀ := σ) hPlip
    exact this
  have hk : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ J →
      ∫ σ, (deriv P σ + F σ) * deriv ψ σ = 0 := by
    intro ψ hψ hψc hψJ
    have hweak := hr.oneDimensional_limit_weak_equation h hV hval hlim he h1D hψ hψc
      (hψJ.trans hδO)
    have hψ'c : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
    have hint1 : Integrable (fun σ ↦ deriv P σ * deriv ψ σ) := by
      have hi := (hψ'c.integrable_of_hasCompactSupport (μ := volume) hψc.deriv).mul_bdd
        (measurable_deriv P).aestronglyMeasurable (Eventually.of_forall hdb)
      simpa only [mul_comm] using hi
    have hint2 : Integrable (fun σ ↦ F σ * deriv ψ σ) :=
      (hFc.mul hψ'c).integrable_of_hasCompactSupport hψc.deriv.mul_left
    have hint3 : Integrable (fun σ ↦ f (P σ) * ψ σ) :=
      (hfP.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
    obtain ⟨M₀, hM₀⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : ℝ)
    set M := max M₀ 0 with hMdef
    have hM0 : 0 ≤ M := le_max_right _ _
    have hψzero : ∀ σ, M < |σ| → ψ σ = 0 := by
      intro σ hσ
      apply image_eq_zero_of_notMem_tsupport
      intro hσs
      have := hM₀ hσs
      rw [mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith [le_max_left M₀ 0]
    have hbot : Tendsto (fun σ ↦ F σ * ψ σ) atBot (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_atBot (-M)] with σ hσ
      have : ψ σ = 0 := hψzero σ (by rw [abs_of_neg (by linarith)]; linarith)
      simp [this]
    have htop : Tendsto (fun σ ↦ F σ * ψ σ) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop M] with σ hσ
      have : ψ σ = 0 := hψzero σ (by rw [abs_of_pos (by linarith)]; exact hσ)
      simp [this]
    have hibp := integral_mul_deriv_eq_deriv_mul (u := F) (v := ψ) (u' := fun σ ↦ f (P σ))
      (v' := deriv ψ) (a' := 0) (b' := 0) (fun σ _ ↦ hF σ)
      (fun σ _ ↦ (hψ.differentiable (by simp) σ).hasDerivAt) hint2 hint3 hbot htop
    have hsplit : ∫ σ, (deriv P σ + F σ) * deriv ψ σ =
        (∫ σ, deriv P σ * deriv ψ σ) + ∫ σ, F σ * deriv ψ σ := by
      rw [← integral_add hint1 hint2]
      congr 1
      funext σ
      ring
    rw [hsplit, hweak, hibp]
    ring
  have hloc : LocallyIntegrableOn (fun σ ↦ deriv P σ + F σ) J := by
    apply LocallyIntegrable.locallyIntegrableOn
    refine ((Continuous.locallyIntegrable (continuous_const (y := κ))).mono
      (measurable_deriv P).aestronglyMeasurable (Eventually.of_forall fun σ ↦ ?_)).add
      hFc.locallyIntegrable
    rw [Real.norm_eq_abs κ]
    exact (hdb σ).trans (le_abs_self κ)
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_mul_deriv_eq_zero hJo hJc
    ⟨τ₀, Metric.mem_ball_self hδ⟩ hloc hk
  set G : ℝ → ℝ := fun σ ↦ P τ₀ + ∫ r in τ₀..σ, (c - F r) with hGdef
  have hGd : ∀ σ, HasDerivAt G (c - F σ) σ := fun σ ↦
    ((continuous_const.sub hFc).integral_hasStrictDerivAt τ₀ σ).hasDerivAt.const_add _
  have hPG : ∀ σ ∈ J, P σ = G σ := by
    intro σ hσ
    have hsub : uIcc τ₀ σ ⊆ J := hJc.uIcc_subset (Metric.mem_ball_self hδ) hσ
    have hac := (hPlip.lipschitzOnWith (s := uIcc τ₀ σ)).absolutelyContinuousOnInterval
    have hftc := hac.integral_deriv_eq_sub
    have hcongr : ∫ r in τ₀..σ, deriv P r = ∫ r in τ₀..σ, (c - F r) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hc] with r hr hrI
      have hrJ : r ∈ J := hsub (uIoc_subset_uIcc hrI)
      linarith [hr hrJ]
    rw [hGdef]
    simp only
    linarith
  have hderivJ : ∀ σ ∈ J, HasDerivAt P (c - F σ) σ := by
    intro σ hσ
    exact (hGd σ).congr_of_eventuallyEq (by
      filter_upwards [hJo.mem_nhds hσ] with r hr
      exact hPG r hr)
  have hd₀ := hderivJ τ₀ (Metric.mem_ball_self hδ)
  refine ⟨by rwa [hd₀.deriv], ?_⟩
  have heq : deriv P =ᶠ[𝓝 τ₀] fun σ ↦ c - F σ := by
    filter_upwards [hJo.mem_nhds (Metric.mem_ball_self hδ)] with σ hσ
    exact (hderivJ σ hσ).deriv
  exact ((continuous_const.sub hFc).continuousAt).congr heq.symm

/-- **HA9.a for microscopic limits.** A one-dimensional physical translation limit `V` (depending
only on `⟪e, x⟫`) has a Hamiltonian profile `P τ = V (τ • e)`: `P` is `C¹` on its positive set
with `P'² = 2 W(P)` there. -/
theorem RigidityHypotheses.isHamiltonianProfile_of_oneDimensional_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    {p : ℕ → Space (m + 1)} {V : Space (m + 1) → ℝ}
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (h1D : ∀ x, V x = V ((inner ℝ e x) • e)) :
    IsHamiltonianProfile f (fun τ ↦ V (τ • e)) (deriv (fun τ ↦ V (τ • e))) := by
  have hPc : Continuous (fun τ : ℝ ↦ V (τ • e)) :=
    hV.continuous.comp (continuous_id.smul continuous_const)
  have hPval : ∀ τ : ℝ, V (τ • e) ∈ Icc (0 : ℝ) 1 := fun τ ↦ hval _
  have hreg := fun (τ : ℝ) (hτ : 0 < V (τ • e)) ↦
    hr.oneDimensional_limit_regular h hV hval hlim he h1D hτ
  refine ⟨hPc, hPval, fun τ hτ ↦ (hreg τ hτ).1, fun τ hτ ↦ (hreg τ hτ).2, ?_⟩
  have hO : IsOpen {τ : ℝ | 0 < V (τ • e)} := isOpen_lt continuous_const hPc
  have hae := hr.oneDimensional_limit_hamiltonian_ae_eq_zero h hbound hV hval hlim he h1D
  have hk : (fun τ : ℝ ↦ deriv (fun τ : ℝ ↦ V (τ • e)) τ ^ 2 -
      2 * normalizedPotential f (V (τ • e)))
      =ᵐ[volume.restrict {τ : ℝ | 0 < V (τ • e)}] fun _ ↦ (0 : ℝ) := by
    rw [EventuallyEq, ae_restrict_iff' hO.measurableSet]
    filter_upwards [hae] with τ hτ hτO
    rw [layerHamiltonian, indicator_of_mem (show τ ∈ {σ : ℝ | 0 < V (σ • e)} from hτO)] at hτ
    linarith
  have hkc : ContinuousOn
      (fun τ : ℝ ↦ deriv (fun τ : ℝ ↦ V (τ • e)) τ ^ 2 - 2 * normalizedPotential f (V (τ • e)))
      {τ : ℝ | 0 < V (τ • e)} := by
    intro τ hτ
    apply ContinuousAt.continuousWithinAt
    exact ((hreg τ hτ).2.pow 2).sub (continuousAt_const.mul
      ((h.normalizedPotential_continuousOn.comp_continuous hPc hPval).continuousAt))
  have heqOn := Measure.eqOn_open_of_ae_eq hk hO hkc continuousOn_const
  intro τ hτ
  have := heqOn hτ
  simp only at this
  linarith

end SerrinEpigraph
