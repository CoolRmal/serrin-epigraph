module

public import SerrinEpigraph.DiffuseNormalKinetic
public import SerrinEpigraph.IntegrationByParts
public import SerrinEpigraph.WeakEquation
public import SerrinEpigraph.CylinderSlicing

/-!
# HA4: harmonicity of the height limit, and the aligned harmonic layer data

The last input of the HA0 tilt decay (`SerrinEpigraph.DiffuseNormalKinetic`,
`RigidityHypotheses.hasCylinderTiltDecay_of_harmonicLayerData`) is
`HasAlignedHarmonicLayerData g u σ M`: along aligned HA11 sequences, a harmonic `C²` function
`H` with the weighted height approximation (HA6.1) and the flux limit (HA4). This module proves
the harmonicity part of HA4 (blueprint `harmonic-approximation.md`, end of HA4):

* if the normalized heights have a limit `H ∈ L²(B_{3/4})` with weak gradient
  `G ∈ L²(B_{3/4})`, the weighted height approximation holds for `H`, and the normalized fluxes
  `F_j = ε ∂ₜ v_j ∇_y v_j / δ_j` converge weakly to `-σ G ⊗ δ_{t=0}`, then FE4 (the flux of a
  horizontal gradient is controlled by the energy away from the plane, which is `o(δ_j²)` by the
  FE3 tails) forces `∫ ⟪G, ∇ϕ⟫ = 0`; hence `H` is very weakly harmonic, Weyl's lemma gives a
  smooth harmonic representative `H'`, the weak gradient is `∇H'` almost everywhere, and a cutoff
  of `H'` is a global `C²` function, harmonic near `B̄_{1/2}`, with the same bounds and limits.

The remaining input is the weak height data `HasAlignedWeakHeightData g u σ M`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ}

/-! ## Weak gradients and the Laplacian -/

/-- With a weak gradient `G` of `H` on `B` (tested against `C¹` functions), the distributional
Laplacian of `H` pairs as `∫ H Δϕ = -∫ ⟪G, ∇ϕ⟫`. -/
theorem integral_mul_laplacian_eq_neg_of_weakGradient {d : ℕ} {B : Set (Space d)}
    {H : Space d → ℝ} {G : Space d → Space d} (hHi : IntegrableOn H B) (hGi : IntegrableOn G B)
    (hweak : ∀ ϕ : Space d → ℝ, ContDiff ℝ 1 ϕ → HasCompactSupport ϕ → tsupport ϕ ⊆ B →
      ∀ w : Space d, (∫ y, H y * fderiv ℝ ϕ y w) = -∫ y, ϕ y * inner ℝ (G y) w)
    {ϕ : Space d → ℝ} (hϕ : ContDiff ℝ 2 ϕ) (hcϕ : HasCompactSupport ϕ) (hsub : tsupport ϕ ⊆ B) :
    (∫ y, H y * Δ ϕ y) = -∫ y, inner ℝ (G y) (gradient ϕ y) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hϕ1 : ContDiff ℝ 1 (fderiv ℝ ϕ) := hϕ.fderiv_right (by norm_num)
  have hϕi : ∀ i, ContDiff ℝ 1 (fun y ↦ fderiv ℝ ϕ y (b i)) := fun i ↦
    hϕ1.clm_apply contDiff_const
  have hsupp : ∀ i, tsupport (fun y ↦ fderiv ℝ ϕ y (b i)) ⊆ tsupport ϕ := fun i ↦
    closure_minimal (fun y hy ↦ by
      by_contra hn
      exact hy (by simp [fderiv_of_notMem_tsupport ℝ hn])) (isClosed_tsupport ϕ)
  have hcϕi : ∀ i, HasCompactSupport (fun y ↦ fderiv ℝ ϕ y (b i)) := fun i ↦
    hcϕ.mono' (subset_tsupport _ |>.trans (hsupp i))
  have hdiff : ∀ y, DifferentiableAt ℝ (fderiv ℝ ϕ) y := fun y ↦
    (hϕ1.differentiable one_ne_zero) y
  have hlap : ∀ y, Δ ϕ y = ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ ϕ z (b i)) y (b i) := fun y ↦
    laplacian_eq_sum_fderiv b (hdiff y)
  -- integrability of the terms
  have hint : ∀ i, Integrable (fun y ↦ H y * fderiv ℝ (fun z ↦ fderiv ℝ ϕ z (b i)) y (b i)) := by
    intro i
    have hc : Continuous (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ ϕ z (b i)) y (b i)) :=
      ((hϕi i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hK := (hcϕi i).isCompact
    have h1 : IntegrableOn (fun y ↦ H y * fderiv ℝ (fun z ↦ fderiv ℝ ϕ z (b i)) y (b i))
        (tsupport (fun y ↦ fderiv ℝ ϕ y (b i))) :=
      (hHi.mono_set ((hsupp i).trans hsub)).mul_continuousOn hc.continuousOn hK
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
    intro y hy
    by_contra hn
    apply hy
    have h0 : fderiv ℝ (fun z ↦ fderiv ℝ ϕ z (b i)) y = 0 := fderiv_of_notMem_tsupport ℝ hn
    simp [h0]
  rw [show (fun y ↦ H y * Δ ϕ y) =
      fun y ↦ ∑ i, H y * fderiv ℝ (fun z ↦ fderiv ℝ ϕ z (b i)) y (b i) by
    funext y
    rw [hlap y, Finset.mul_sum], integral_finsetSum _ fun i _ ↦ hint i]
  have hterm : ∀ i, (∫ y, H y * fderiv ℝ (fun z ↦ fderiv ℝ ϕ z (b i)) y (b i)) =
      -∫ y, fderiv ℝ ϕ y (b i) * inner ℝ (G y) (b i) :=
    fun i ↦ hweak _ (hϕi i) (hcϕi i) ((hsupp i).trans hsub) (b i)
  simp only [hterm, Finset.sum_neg_distrib]
  congr 1
  have hint2 : ∀ i, Integrable (fun y ↦ fderiv ℝ ϕ y (b i) * inner ℝ (G y) (b i)) := by
    intro i
    have hc : Continuous (fun y ↦ fderiv ℝ ϕ y (b i)) := (hϕi i).continuous
    have hK := (hcϕi i).isCompact
    have h1 : IntegrableOn (fun y ↦ fderiv ℝ ϕ y (b i) * inner ℝ (G y) (b i))
        (tsupport (fun y ↦ fderiv ℝ ϕ y (b i))) :=
      IntegrableOn.continuousOn_mul hc.continuousOn
        (Integrable.inner_const (𝕜 := ℝ) (hGi.mono_set ((hsupp i).trans hsub)) (b i)) hK
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
    intro y hy
    by_contra hn
    apply hy
    have h0 : fderiv ℝ ϕ y (b i) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y ↦ fderiv ℝ ϕ y (b i)) hn
    simp [h0]
  rw [← integral_finsetSum _ fun i _ ↦ hint2 i]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only
  rw [← b.sum_inner_mul_inner (G y) (gradient ϕ y)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm (gradient ϕ y) (b i), inner_gradient_left, mul_comm]

/-! ## The flux of a horizontal gradient vanishes in the limit (FE4 with FE3) -/

variable {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- Along an aligned HA11 sequence, the normalized flux tested against a horizontal gradient
`∇ϕ` and a vertical cutoff `ψ`, constant near the plane, tends to zero: by FE4 it equals
`δ⁻¹ ∫ ϕ ψ' (e - ε ∂ₜv²)`, and the energy where `ψ' ≠ 0` is `o(δ²)` (FE3 tails). -/
theorem RigidityHypotheses.tendsto_flux_gradient_of_aligned
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (x : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hRδ : Tendsto (fun j ↦ R j * δ j) atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x j + R j • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0))
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    (hQ : Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e))
    {ϕ : Space m → ℝ} (hϕ : ContDiff ℝ 1 ϕ) (hcϕ : HasCompactSupport ϕ)
    (hϕs : tsupport ϕ ⊆ ball (0 : Space m) 1)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo (-1) 1) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hψ0 : ∀ t, |t| < c₀ → deriv ψ t = 0) :
    Tendsto (fun j ↦ ∫ z, ψ (z (Fin.last m)) * inner ℝ (gradient ϕ (horizontal z))
      (((δ j)⁻¹ * (R j)⁻¹ *
          verticalDerivative (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z) •
        horizontal (gradient (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z))) atTop
      (𝓝 0) := by
  obtain ⟨Mϕ, hMϕ⟩ := hϕ.continuous.bounded_above_of_compact_support hcϕ
  have hdψc : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hcdψ : HasCompactSupport (deriv ψ) := hcψ.mono' (support_deriv_subset)
  obtain ⟨C', hC'⟩ := hdψc.bounded_above_of_compact_support hcdψ
  have hC'0 : 0 ≤ C' := (norm_nonneg _).trans (hC' 0)
  have hMϕ0 : 0 ≤ Mϕ := (norm_nonneg _).trans (hMϕ 0)
  set A : Set (Space (m + 1)) :=
    tiltCylinder (verticalDirection m) 1 ∩ {z | c₀ ≤ |z (Fin.last m)|} with hA
  have hT := hr.tendsto_energy_tail_of_aligned h hsharp x hR hRt hδ hRδ he hlocal hQ
    (r := 1) one_pos hc₀
  have hlim : Tendsto (fun j ↦ Mϕ * C' * (δ j * ((δ j)⁻¹ ^ 2 * ∫ z in A,
      rescaledPhaseEnergyDensity f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z)))
      atTop (𝓝 0) := by
    have := (hδ0.mul hT).const_mul (Mϕ * C')
    rwa [mul_zero, mul_zero] at this
  refine squeeze_zero_norm (fun j ↦ ?_) hlim
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x j + R j • Q j z) with hvdef
  have hvL : LocallyLipschitz v :=
    locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz _ _ _
  have hval : ∀ z, v z ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hRj := hR j
  have hδj := hδ j
  have hE0 : ∀ z, 0 ≤ rescaledPhaseEnergyDensity f (R j) v z :=
    hr.rescaledPhaseEnergyDensity_nonneg h hRj.le hval
  have hiE : ∀ K : Set (Space (m + 1)), IsCompact K →
      IntegrableOn (rescaledPhaseEnergyDensity f (R j) v) K :=
    fun K hK ↦ h.integrableOn_rescaledPhaseEnergy hvL hval (R j) hK
  -- rewrite the flux as `δ⁻¹` times the FE4 left side
  have heq : (∫ z, ψ (z (Fin.last m)) * inner ℝ (gradient ϕ (horizontal z))
      (((δ j)⁻¹ * (R j)⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) =
      (δ j)⁻¹ * ∫ z, (R j)⁻¹ * ψ (z (Fin.last m)) * verticalDerivative v z *
        inner ℝ (horizontal (gradient v z)) (gradient ϕ (horizontal z)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    simp only
    rw [real_inner_smul_right, real_inner_comm]
    ring
  have hbound := rescaled_horizontal_flux_bound hRj (fun z ↦ (hval z).1) hvL
    (hr.rescaled_isometry_modica_bound h (x j) hRj (Q j)) hiE
    (fun X hX hcX ↦ hr.rescaled_isometry_stress_stationarity h _ hRj _ _ hX hcX)
    hϕ hcϕ (fun y ↦ by have := hMϕ y; rwa [Real.norm_eq_abs] at this) hψ hcψ
  -- the region where `ϕ(y) ψ'(t) ≠ 0` lies in `A`
  have hsub : {z : Space (m + 1) | horizontal z ∈ tsupport ϕ ∧
      z (Fin.last m) ∈ tsupport (deriv ψ)} ⊆ A := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have h1 : ‖horizontal z‖ < 1 := by
      have := hϕs hz1
      rwa [mem_ball, dist_zero_right] at this
    have h2 : z (Fin.last m) ∈ Ioo (-1) 1 := hψs (tsupport_deriv_subset hz2)
    have h3 : c₀ ≤ |z (Fin.last m)| := by
      have hcl : IsClosed {t : ℝ | c₀ ≤ |t|} := isClosed_le continuous_const continuous_abs
      have hsupp : Function.support (deriv ψ) ⊆ {t : ℝ | c₀ ≤ |t|} := fun t ht ↦ by
        by_contra hlt
        exact ht (hψ0 t (not_le.mp hlt))
      exact closure_minimal hsupp hcl hz2
    refine ⟨mem_tiltCylinder_vertical_iff.mpr ⟨h1, abs_lt.mpr h2⟩, h3⟩
  have hSm : MeasurableSet {z : Space (m + 1) | horizontal z ∈ tsupport ϕ ∧
      z (Fin.last m) ∈ tsupport (deriv ψ)} :=
    ((isClosed_tsupport ϕ).measurableSet.preimage continuous_horizontal.measurable).inter
      ((isClosed_tsupport (deriv ψ)).measurableSet.preimage continuous_last.measurable)
  have hAb : A ⊆ closedBall (0 : Space (m + 1)) 2 := by
    have h1 := ha6_tiltCylinder_subset_closedBall (m := m) 1
    rw [mul_one] at h1
    exact inter_subset_left.trans h1
  have hiA : IntegrableOn (rescaledPhaseEnergyDensity f (R j) v) A :=
    (hiE _ (isCompact_closedBall _ 2)).mono_set hAb
  have hint2 : (∫ z in {z : Space (m + 1) | horizontal z ∈ tsupport ϕ ∧
      z (Fin.last m) ∈ tsupport (deriv ψ)},
        |deriv ψ (z (Fin.last m))| * rescaledPhaseEnergyDensity f (R j) v z) ≤
      C' * ∫ z in A, rescaledPhaseEnergyDensity f (R j) v z := by
    rw [← integral_const_mul]
    calc (∫ z in {z : Space (m + 1) | horizontal z ∈ tsupport ϕ ∧
          z (Fin.last m) ∈ tsupport (deriv ψ)},
            |deriv ψ (z (Fin.last m))| * rescaledPhaseEnergyDensity f (R j) v z)
        ≤ ∫ z in {z : Space (m + 1) | horizontal z ∈ tsupport ϕ ∧
          z (Fin.last m) ∈ tsupport (deriv ψ)}, C' * rescaledPhaseEnergyDensity f (R j) v z := by
          refine setIntegral_mono_on ?_ ((hiA.mono_set hsub).const_mul C') hSm fun z _ ↦ ?_
          · have := hr.integrableOn_rescaledEnergy_mul_bounded h hvL hval hRj.le
              ((isBounded_closedBall (x := (0 : Space (m + 1))) (r := 2)).subset
                (hsub.trans hAb)) (k := fun z ↦ |deriv ψ (z (Fin.last m))|)
              (continuous_abs.comp (hdψc.comp continuous_last)).measurable (K := C')
              (fun z _ ↦ by rw [abs_abs]; have := hC' (z (Fin.last m)); rwa [Real.norm_eq_abs] at this)
              hSm
            refine this.congr_fun (fun z _ ↦ ?_) hSm
            simp only
            ring
          · have := hC' (z (Fin.last m))
            rw [Real.norm_eq_abs] at this
            exact mul_le_mul_of_nonneg_right this (hE0 z)
      _ ≤ ∫ z in A, C' * rescaledPhaseEnergyDensity f (R j) v z :=
          setIntegral_mono_set (hiA.const_mul C')
            (Eventually.of_forall fun z ↦ mul_nonneg hC'0 (hE0 z)) (Eventually.of_forall hsub)
  rw [heq, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδj)]
  have hX0 : 0 ≤ ∫ z in A, rescaledPhaseEnergyDensity f (R j) v z :=
    setIntegral_nonneg ((isOpen_tiltCylinder _ _).measurableSet.inter
      (isClosed_le continuous_const (continuous_abs.comp continuous_last)).measurableSet)
      fun z _ ↦ hE0 z
  calc (δ j)⁻¹ * |∫ z, (R j)⁻¹ * ψ (z (Fin.last m)) * verticalDerivative v z *
        inner ℝ (horizontal (gradient v z)) (gradient ϕ (horizontal z))|
      ≤ (δ j)⁻¹ * (Mϕ * (C' * ∫ z in A, rescaledPhaseEnergyDensity f (R j) v z)) := by
        refine mul_le_mul_of_nonneg_left (hbound.trans ?_) (inv_nonneg.mpr hδj.le)
        exact mul_le_mul_of_nonneg_left hint2 hMϕ0
    _ = Mϕ * C' * (δ j * ((δ j)⁻¹ ^ 2 * ∫ z in A, rescaledPhaseEnergyDensity f (R j) v z)) := by
        field_simp

/-! ## The weak height data -/

/-- **The weak height data along one aligned HA11 sequence.** A subsequence `φ`, a function
`H ∈ L²(B_{3/4})` with weak gradient `G ∈ L²(B_{3/4})` (tested against `C¹` functions supported
in `B_{3/4}`), `L²` bounds `M`, and centers `a j → 0`, such that

* **(HA6.1)** `∫_{Q_{1/2}} ((t - a_j)/δ_j - H(y))² ε |∇v_j|² → 0`;
* **(HA4.1)** the normalized fluxes `F_j = ε ∂ₜ v_j ∇_y v_j / δ_j` converge weakly to
  `-σ G ⊗ δ_{t=0}`: `∫ ψ(t) ⟪ζ(y), F_j⟫ → -σ ψ(0) ∫ ⟪ζ, G⟫` for continuous `ζ` supported in
  `B_{3/4}` and continuous `ψ` supported in `(-1/2, 1/2)`.

Here `H` is the limit of the normalized level heights (HA2, HA3) and `G` its weak gradient. -/
def AlignedWeakHeightConclusion (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (σ M : ℝ)
    (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (H : Space m → ℝ) (G : Space m → Space m) (a : ℕ → ℝ),
    MemLp H 2 (volume.restrict (ball (0 : Space m) (3 / 4))) ∧
    MemLp G 2 (volume.restrict (ball (0 : Space m) (3 / 4))) ∧
    (∫ y in ball (0 : Space m) (3 / 4), H y ^ 2) ≤ M ∧
    (∫ y in ball (0 : Space m) (3 / 4), ‖G y‖ ^ 2) ≤ M ∧
    (∀ ϕ : Space m → ℝ, ContDiff ℝ 1 ϕ → HasCompactSupport ϕ →
      tsupport ϕ ⊆ ball (0 : Space m) (3 / 4) → ∀ w : Space m,
        (∫ y, H y * fderiv ℝ ϕ y w) = -∫ y, ϕ y * inner ℝ (G y) w) ∧
    Tendsto a atTop (𝓝 0) ∧
    Tendsto (fun j ↦ ∫ z in tiltCylinder (verticalDirection m) (1 / 2),
      ((z (Fin.last m) - a j) / δ (φ j) - H (horizontal z)) ^ 2 *
        ((R (φ j))⁻¹ * ‖gradient (fun z ↦ zeroExtension g u
          (x (φ j) + R (φ j) • Q (φ j) z)) z‖ ^ 2)) atTop (𝓝 0) ∧
    ∀ ζ : Space m → Space m, Continuous ζ → tsupport ζ ⊆ ball (0 : Space m) (3 / 4) →
      ∀ ψ : ℝ → ℝ, Continuous ψ → tsupport ψ ⊆ Ioo (-(1 / 2)) (1 / 2) →
      Tendsto (fun j ↦ ∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z))
        (((δ (φ j))⁻¹ * (R (φ j))⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u
            (x (φ j) + R (φ j) • Q (φ j) z)) z) •
          horizontal (gradient (fun z ↦ zeroExtension g u
            (x (φ j) + R (φ j) • Q (φ j) z)) z))) atTop
        (𝓝 (-(σ * ψ 0) * ∫ y, inner ℝ (ζ y) (G y)))

/-- **The remaining input: weak height data along aligned HA11 sequences** (HA2, HA3, HA5,
HA6.1, HA9, HA10 for the heights, HA1, HA11 weights and the level tails for the flux). -/
def HasAlignedWeakHeightData (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (σ M : ℝ) : Prop :=
  ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ) (e : Space (m + 1)),
    (∀ j, x j ∈ frontier (epigraph g)) → (∀ j, 0 < R j) → Tendsto R atTop atTop →
    (∀ j, 0 < δ j) → Tendsto δ atTop (𝓝 0) → Tendsto (fun j ↦ R j * δ j) atTop atTop →
    (∀ j, cylinderTilt (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) 2
      (verticalDirection m) = δ j ^ 2) →
    ‖e‖ = 1 →
    (∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x j + R j • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0)) →
    Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e) →
    AlignedWeakHeightConclusion g u σ M x R Q δ

/-! ## HA4: the weak height limit is harmonic -/

/-- **HA4 (harmonicity) and regularization.** Along an aligned HA11 sequence, the weak height
data give the harmonic layer conclusion: the weak gradient pairs to zero with every horizontal
gradient (flux limit against FE4 with FE3 tails), so `H` is very weakly harmonic on `B_{3/4}`;
Weyl's lemma, the identification of the weak gradient and a cutoff produce a global `C²`
function, harmonic on `B_{5/8}`, equal to `H` almost everywhere on `B_{5/8}`. -/
theorem RigidityHypotheses.harmonicLayerConclusion_of_weak
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (x : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hRδ : Tendsto (fun j ↦ R j * δ j) atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x j + R j • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0))
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    (hQ : Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e)) {M : ℝ}
    (hw : AlignedWeakHeightConclusion g u (phasePrimitive f 1) M x R Q δ) :
    HarmonicLayerConclusion g u (phasePrimitive f 1) M x R Q δ := by
  obtain ⟨φ, hφ, H, G, a, hH2, hG2, hMH, hMG, hweak, ha0, hI1, hI2⟩ := hw
  set B : Set (Space m) := ball (0 : Space m) (3 / 4) with hB
  have : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hHi : IntegrableOn H B := hH2.integrable one_le_two
  have hGi : IntegrableOn G B := hG2.integrable one_le_two
  have hσ : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  -- the vertical cutoff
  let bψ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 3 / 8, by norm_num, by norm_num⟩
  have htsψ : tsupport (⇑bψ) = closedBall 0 (3 / 8) := bψ.tsupport_eq
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
  have hψs : tsupport (⇑bψ) ⊆ Ioo (-(1 / 2)) (1 / 2) := by
    rw [htsψ]
    intro t ht
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have hψs1 : tsupport (⇑bψ) ⊆ Ioo (-1) 1 := hψs.trans (Ioo_subset_Ioo (by norm_num) (by norm_num))
  -- step 1: `∫ ⟪∇ϕ, G⟫ = 0`
  have hGgrad : ∀ ϕ : Space m → ℝ, ContDiff ℝ 1 ϕ → HasCompactSupport ϕ → tsupport ϕ ⊆ B →
      (∫ y, inner ℝ (gradient ϕ y) (G y)) = 0 := by
    intro ϕ hϕ hcϕ hsub
    have hgs : tsupport (gradient ϕ) ⊆ B := by
      refine (closure_minimal (fun y hy ↦ ?_) (isClosed_tsupport ϕ)).trans hsub
      by_contra hn
      exact hy (ha6_gradient_eq_zero_of_notMem_tsupport hn)
    have h1 := hI2 (gradient ϕ) (ha6_continuous_gradient hϕ) hgs (⇑bψ) bψ.continuous hψs
    have h2 := (hr.tendsto_flux_gradient_of_aligned h hsharp x hR hRt hδ hδ0 hRδ he hlocal hQ hϕ
      hcϕ (hsub.trans (ball_subset_ball (by norm_num))) bψ.contDiff bψ.hasCompactSupport hψs1
      (c₀ := 1 / 4) (by norm_num) hdψ).comp hφ.tendsto_atTop
    have h3 := tendsto_nhds_unique h1 h2
    rw [hψ0, mul_one] at h3
    have h4 : phasePrimitive f 1 * (∫ y, inner ℝ (gradient ϕ y) (G y)) = 0 := by linarith
    exact (mul_eq_zero.mp h4).resolve_left hσ.ne'
  -- step 2: very weak harmonicity and Weyl's lemma
  have hvwh : IsVeryWeaklyHarmonicOn B H := by
    refine ⟨hHi.locallyIntegrableOn, fun ϕ hϕ hcϕ hsub ↦ ?_⟩
    have hϕ2 : ContDiff ℝ 2 ϕ := hϕ.of_le (by norm_num)
    rw [integral_mul_laplacian_eq_neg_of_weakGradient hHi hGi hweak hϕ2 hcϕ hsub]
    have h1 := hGgrad ϕ (hϕ.of_le (by exact_mod_cast le_top)) hcϕ hsub
    have h2 : (fun y ↦ inner ℝ (G y) (gradient ϕ y)) = fun y ↦ inner ℝ (gradient ϕ y) (G y) :=
      funext fun y ↦ real_inner_comm _ _
    rw [h2, h1, neg_zero]
  obtain ⟨H', hH'c, hΔ', hae⟩ := weyl_lemma isOpen_ball hvwh
  have hH'1 : ContDiffOn ℝ 1 H' B := hH'c.of_le (by exact_mod_cast le_top)
  have haeB : ∀ᵐ y, y ∈ B → H y = H' y := (ae_restrict_iff' measurableSet_ball).mp hae
  -- step 3: the weak gradient is the classical gradient of `H'`
  have hgradc : ContinuousOn (gradient H') B :=
    (toDual ℝ (Space m)).symm.continuous.comp_continuousOn
      (hH'1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)
  have hGeq : ∀ᵐ y, y ∈ B → G y - gradient H' y = 0 := by
    refine isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hGi.locallyIntegrableOn.sub (hgradc.locallyIntegrableOn measurableSet_ball))
      fun ϕ hϕ hcϕ hsub ↦ ?_
    have hϕ1 : ContDiff ℝ 1 ϕ := hϕ.of_le (by exact_mod_cast le_top)
    have hK := hcϕ.isCompact
    have hint : Integrable (fun y ↦ ϕ y • (G y - gradient H' y)) := by
      have h1 : IntegrableOn (fun y ↦ ϕ y • (G y - gradient H' y)) (tsupport ϕ) :=
        IntegrableOn.continuousOn_smul
          ((hGi.mono_set hsub).sub ((hgradc.mono hsub).integrableOn_compact hK))
          hϕ.continuous.continuousOn hK
      refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
      intro y hy
      by_contra hn
      exact hy (by simp [image_eq_zero_of_notMem_tsupport hn])
    set V : Space m := ∫ y, ϕ y • (G y - gradient H' y) with hV
    have hVV : inner ℝ V V = 0 := by
      have e1 : inner ℝ V V = ∫ y, inner ℝ V (ϕ y • (G y - gradient H' y)) :=
        (integral_inner hint V).symm
      have hHfd : Integrable (fun y ↦ H y * fderiv ℝ ϕ y V) := by
        have hc : Continuous (fun y ↦ fderiv ℝ ϕ y V) :=
          (hϕ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
        have h1 : IntegrableOn (fun y ↦ H y * fderiv ℝ ϕ y V) (tsupport ϕ) :=
          (hHi.mono_set hsub).mul_continuousOn hc.continuousOn hK
        refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
        intro y hy
        by_contra hn
        exact hy (by simp [fderiv_of_notMem_tsupport ℝ hn])
      have e2 : (∫ y, H y * fderiv ℝ ϕ y V) = ∫ y, H' y * fderiv ℝ ϕ y V := by
        refine integral_congr_ae ?_
        filter_upwards [haeB] with y hy
        by_cases hyt : y ∈ tsupport ϕ
        · rw [hy (hsub hyt)]
        · simp [fderiv_of_notMem_tsupport ℝ hyt]
      have e3 := integral_mul_fderiv_eq_neg_of_hasCompactSupport (μ := volume) isOpen_ball hH'1 hϕ1
        hcϕ hsub V
      have e4 := hweak ϕ hϕ1 hcϕ hsub V
      have hint1 : Integrable (fun y ↦ ϕ y * inner ℝ (G y) V) := by
        have h1 : IntegrableOn (fun y ↦ ϕ y * inner ℝ (G y) V) (tsupport ϕ) :=
          IntegrableOn.continuousOn_mul hϕ.continuous.continuousOn
            (Integrable.inner_const (𝕜 := ℝ) (hGi.mono_set hsub) V) hK
        refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
        intro y hy
        by_contra hn
        exact hy (by simp [image_eq_zero_of_notMem_tsupport hn])
      have hint2 : Integrable (fun y ↦ fderiv ℝ H' y V * ϕ y) := by
        have hc : ContinuousOn (fun y ↦ fderiv ℝ H' y V) B :=
          (hH'1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const
        have h1 : IntegrableOn (fun y ↦ fderiv ℝ H' y V * ϕ y) (tsupport ϕ) :=
          IntegrableOn.mul_continuousOn ((hc.mono hsub).integrableOn_compact hK)
            hϕ.continuous.continuousOn hK
        refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
        intro y hy
        by_contra hn
        exact hy (by simp [image_eq_zero_of_notMem_tsupport hn])
      have e5 : (∫ y, inner ℝ V (ϕ y • (G y - gradient H' y))) =
          (∫ y, ϕ y * inner ℝ (G y) V) - ∫ y, fderiv ℝ H' y V * ϕ y := by
        rw [← integral_sub hint1 hint2]
        refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
        simp only
        rw [real_inner_smul_right, inner_sub_right, real_inner_comm V (G y),
          real_inner_comm (gradient H' y) V, inner_gradient_left]
        ring
      rw [e1, e5, ← neg_neg (∫ y, ϕ y * inner ℝ (G y) V), ← e4, e2, e3]
      ring
    have hV0 : V = 0 := inner_self_eq_zero.mp hVV
    exact hV0
  have hGB : ∀ᵐ y, y ∈ B → G y = gradient H' y := by
    filter_upwards [hGeq] with y hy hyB
    exact sub_eq_zero.mp (hy hyB)
  -- step 4: a global `C²` representative, harmonic on `B_{5/8}`
  let bκ : ContDiffBump (0 : Space m) := ⟨5 / 8, 11 / 16, by norm_num, by norm_num⟩
  have htsκ : tsupport (⇑bκ) = closedBall 0 (11 / 16) := bκ.tsupport_eq
  set H'' : Space m → ℝ := fun y ↦ bκ y * H' y with hH''
  have hH''c : ContDiff ℝ 2 H'' := by
    refine contDiff_iff_contDiffAt.mpr fun y ↦ ?_
    by_cases hy : y ∈ B
    · exact (bκ.contDiff.contDiffAt).mul
        ((hH'c.contDiffAt (isOpen_ball.mem_nhds hy)).of_le (by exact_mod_cast le_top))
    · have hyt : y ∉ tsupport (⇑bκ) := by
        rw [htsκ, mem_closedBall, dist_zero_right]
        intro hle
        apply hy
        rw [hB, mem_ball, dist_zero_right]
        linarith
      have hev : H'' =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport (⇑bκ)).isOpen_compl.mem_nhds hyt] with z hz
        simp [hH'', image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  set U : Set (Space m) := ball (0 : Space m) (5 / 8) with hU
  have hUB : U ⊆ B := ball_subset_ball (by norm_num)
  have hH''eq : ∀ y ∈ U, H'' y = H' y := fun y hy ↦ by
    have h1 : bκ y = 1 := bκ.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp [hH'', h1]
  have hH''ev : ∀ y ∈ U, H'' =ᶠ[𝓝 y] H' := fun y hy ↦
    eventually_of_mem (isOpen_ball.mem_nhds hy) hH''eq
  have hΔ'' : ∀ y ∈ U, Δ H'' y = 0 := fun y hy ↦ by
    rw [(laplacian_congr_nhds (hH''ev y hy)).eq_of_nhds]
    exact hΔ' y (hUB hy)
  have hgrad'' : ∀ y ∈ U, gradient H'' y = gradient H' y := fun y hy ↦ by
    simp only [gradient, (hH''ev y hy).fderiv_eq]
  have hball : closedBall (0 : Space m) (1 / 2) ⊆ U := closedBall_subset_ball (by norm_num)
  have hhalf : ball (0 : Space m) (1 / 2) ⊆ U := ball_subset_ball (by norm_num)
  have hH''H : ∀ᵐ y, y ∈ ball (0 : Space m) (1 / 2) → H'' y = H y := by
    filter_upwards [haeB] with y hy hyh
    rw [hH''eq y (hhalf hyh), hy (hUB (hhalf hyh))]
  have hG'' : ∀ᵐ y, y ∈ ball (0 : Space m) (1 / 2) → gradient H'' y = G y := by
    filter_upwards [hGB] with y hy hyh
    rw [hgrad'' y (hhalf hyh), hy (hUB (hhalf hyh))]
  refine ⟨φ, hφ, H'', U, a, isOpen_ball, hball, hH''c, hΔ'', ?_, ?_, ha0, ?_, ?_⟩
  · -- `L²` bound
    calc (∫ y in ball (0 : Space m) (1 / 2), H'' y ^ 2)
        = ∫ y in ball (0 : Space m) (1 / 2), H y ^ 2 :=
          setIntegral_congr_ae measurableSet_ball (by
            filter_upwards [hH''H] with y hy hyh
            rw [hy hyh])
      _ ≤ ∫ y in B, H y ^ 2 :=
          setIntegral_mono_set hH2.integrable_sq (Eventually.of_forall fun y ↦ sq_nonneg _)
            (Eventually.of_forall (ball_subset_ball (by norm_num)))
      _ ≤ M := hMH
  · -- Dirichlet bound
    have hGsq : IntegrableOn (fun y ↦ ‖G y‖ ^ 2) B :=
      (memLp_two_iff_integrable_sq_norm hG2.aestronglyMeasurable).mp hG2
    calc (∫ y in ball (0 : Space m) (1 / 2), ‖gradient H'' y‖ ^ 2)
        = ∫ y in ball (0 : Space m) (1 / 2), ‖G y‖ ^ 2 :=
          setIntegral_congr_ae measurableSet_ball (by
            filter_upwards [hG''] with y hy hyh
            rw [hy hyh])
      _ ≤ ∫ y in B, ‖G y‖ ^ 2 :=
          setIntegral_mono_set hGsq (Eventually.of_forall fun y ↦ sq_nonneg _)
            (Eventually.of_forall (ball_subset_ball (by norm_num)))
      _ ≤ M := hMG
  · -- weighted height approximation
    refine hI1.congr fun j ↦ setIntegral_congr_ae (isOpen_tiltCylinder _ _).measurableSet ?_
    filter_upwards [ae_comp_horizontal hH''H] with z hz hzQ
    have h1 : horizontal z ∈ ball (0 : Space m) (1 / 2) := by
      rw [mem_ball, dist_zero_right]
      exact (mem_tiltCylinder_vertical_iff.mp hzQ).1
    rw [hz h1]
  · -- flux limit
    intro ζ hζ hζs ψ hψ hψs'
    have h1 := hI2 ζ hζ (hζs.trans (ball_subset_ball (by norm_num))) ψ hψ hψs'
    have h2 : (∫ y, inner ℝ (ζ y) (G y)) = ∫ y, inner ℝ (ζ y) (gradient H'' y) := by
      refine integral_congr_ae ?_
      filter_upwards [hG''] with y hy
      by_cases hyt : y ∈ ball (0 : Space m) (1 / 2)
      · rw [hy hyt]
      · have : ζ y = 0 := image_eq_zero_of_notMem_tsupport (fun h' ↦ hyt (hζs h'))
        simp [this]
    rwa [h2] at h1

/-- **HA4 assembled.** The weak height data along aligned sequences give the aligned harmonic
layer data with the same `M`. -/
theorem RigidityHypotheses.hasAlignedHarmonicLayerData_of_weak
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {M : ℝ} (hw : HasAlignedWeakHeightData g u (phasePrimitive f 1) M) :
    HasAlignedHarmonicLayerData g u (phasePrimitive f 1) M := by
  intro x R Q δ e hx hR hRt hδ hδ0 hRδ htilt he hloc hQ
  exact hr.harmonicLayerConclusion_of_weak h hsharp x hR hRt hδ hδ0 hRδ he hloc hQ
    (hw x R Q δ e hx hR hRt hδ hδ0 hRδ htilt he hloc hQ)

/-- The `RigidityReduction` hole from the weak height data. -/
theorem RigidityHypotheses.exists_hasAlignedHarmonicLayerData_of_weak
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (hw : ∃ M : ℝ, 0 ≤ M ∧ HasAlignedWeakHeightData g u (phasePrimitive f 1) M) :
    ∃ M : ℝ, 0 ≤ M ∧ HasAlignedHarmonicLayerData g u (phasePrimitive f 1) M := by
  obtain ⟨M, hM, hwM⟩ := hw
  exact ⟨M, hM, hr.hasAlignedHarmonicLayerData_of_weak h hsharp hwM⟩

end SerrinEpigraph
