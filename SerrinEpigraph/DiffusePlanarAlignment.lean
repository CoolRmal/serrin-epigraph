module

public import SerrinEpigraph.DiffuseHarmonicApproximation
public import SerrinEpigraph.SharpPlaneDensity
public import SerrinEpigraph.DiffuseGoodLayers
public import SerrinEpigraph.CoordCubeMembership

/-!
# Alignment of the HA11 contradiction sequences with their planar blow-down limits

The HA6 inputs `HasHarmonicHeightData` of `SerrinEpigraph.DiffuseHarmonicApproximation` are
stated for arbitrary HA11 contradiction sequences: free-boundary centers `x j`, scales
`R j → ∞`, rotations `Q j` and tilt scales `δ j → 0` with `R j δ j → ∞` and vertical cylinder
tilt `𝓔(2, e_n) = δ j²` of the rotated rescalings `v_j z = zeroExtension g u (x j + R j • Q j z)`.
The level-set machinery of `SerrinEpigraph.DiffuseGoodLayers` (HA2, HA3, HA8, HA9) needs in
addition the planar blow-down limit of the unrotated rescalings, with the positive phase above
the plane in the rotated frame. This module supplies that alignment:

* `verticalReflection`: the reflection `(y, t) ↦ (y, -t)`, with the transfer of gradients,
  vertical derivatives, energy densities and cylinder integrals;
* `RigidityHypotheses.eq_or_eq_neg_of_tilt_tendsto_zero` (HA11, identification of the normal):
  if the tilt along `e'_j → e'` of the blow-downs tends to zero on the unit ball and the
  blow-downs converge to the half-space with normal `e`, then `e' = ± e` (otherwise the kinetic
  mass would vanish while the primitive mass converges to `σ ω_m > 0`);
* `RigidityHypotheses.exists_aligned_subseq` (SD4 + compactness of the sphere): a subsequence
  converges to a half-space through the origin whose normal is the limit of `± Q j e_n`;
* `HasAlignedHarmonicHeightData`: the HA6 inputs for aligned sequences only, and
  `RigidityHypotheses.hasHarmonicHeightData_of_aligned`, which removes the alignment by passing to
  the subsequence and, if needed, replacing `Q j` by `Q j ∘ S` (`S` the vertical reflection),
  `H` by `-H` and the centers `a j` by `-a j`;
* `RigidityHypotheses.tendsto_energy_tail_of_aligned` (FE3 with HA8): along aligned sequences the
  energy of `Q_r` at distance `≥ c` from the plane is `o(δ_j²)` (zero below the plane, stable-well
  exponential decay above it, `δ_j⁻¹ ≤ R_j`);
* the remaining inputs split into the level-set part `HasAlignedHarmonicLayerData` (HA4 flux limit
  and HA6.1 weighted height approximation with a harmonic limit `H`) and the normal kinetic bound
  `HasAlignedNormalKineticBound` (proved in `SerrinEpigraph.DiffuseNormalKinetic`), and
  `RigidityHypotheses.hasCylinderTiltDecay_of_alignedLayerData` gives HA0 from them.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ}

/-! ## The reflection in the horizontal hyperplane -/

/-- The linear map `x ↦ x - 2 xₙ eₙ`. -/
def verticalReflectionLinear (m : ℕ) : Space (m + 1) →ₗ[ℝ] Space (m + 1) where
  toFun x := x - (2 * x (Fin.last m)) • verticalDirection m
  map_add' x y := by
    simp only [PiLp.add_apply, mul_add, add_smul]
    abel
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, smul_sub, smul_smul]
    ring_nf

theorem verticalReflectionLinear_apply (x : Space (m + 1)) :
    verticalReflectionLinear m x = x - (2 * x (Fin.last m)) • verticalDirection m := rfl

theorem horizontal_verticalReflectionLinear (x : Space (m + 1)) :
    horizontal (verticalReflectionLinear m x) = horizontal x := by
  rw [verticalReflectionLinear_apply, ← horizontalContinuousLinearMap_apply, map_sub, map_smul,
    horizontalContinuousLinearMap_apply, horizontalContinuousLinearMap_apply,
    horizontal_verticalDirection, smul_zero, sub_zero]

theorem last_verticalReflectionLinear (x : Space (m + 1)) :
    verticalReflectionLinear m x (Fin.last m) = -x (Fin.last m) := by
  rw [verticalReflectionLinear_apply, PiLp.sub_apply, PiLp.smul_apply, last_verticalDirection,
    smul_eq_mul]
  ring

theorem verticalReflectionLinear_involutive :
    Function.Involutive (verticalReflectionLinear m) := fun x ↦ by
  rw [← point_horizontal_last (verticalReflectionLinear m (verticalReflectionLinear m x)),
    horizontal_verticalReflectionLinear, horizontal_verticalReflectionLinear,
    last_verticalReflectionLinear, last_verticalReflectionLinear, neg_neg,
    point_horizontal_last]

theorem norm_verticalReflectionLinear (x : Space (m + 1)) :
    ‖verticalReflectionLinear m x‖ = ‖x‖ := by
  have h := norm_sq_eq_horizontal_add_last_sq (verticalReflectionLinear m x)
  rw [horizontal_verticalReflectionLinear, last_verticalReflectionLinear, neg_sq,
    ← norm_sq_eq_horizontal_add_last_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The reflection `(y, t) ↦ (y, -t)` in the horizontal hyperplane, as a linear isometry. -/
def verticalReflection (m : ℕ) : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1) :=
  { LinearEquiv.ofInvolutive (verticalReflectionLinear m) verticalReflectionLinear_involutive with
    norm_map' := norm_verticalReflectionLinear }

theorem verticalReflection_apply (x : Space (m + 1)) :
    verticalReflection m x = verticalReflectionLinear m x := rfl

@[simp]
theorem horizontal_verticalReflection (x : Space (m + 1)) :
    horizontal (verticalReflection m x) = horizontal x :=
  horizontal_verticalReflectionLinear x

@[simp]
theorem last_verticalReflection (x : Space (m + 1)) :
    verticalReflection m x (Fin.last m) = -x (Fin.last m) :=
  last_verticalReflectionLinear x

theorem verticalReflection_symm_apply (x : Space (m + 1)) :
    (verticalReflection m).symm x = verticalReflection m x := rfl

@[simp]
theorem verticalReflection_verticalReflection (x : Space (m + 1)) :
    verticalReflection m (verticalReflection m x) = x :=
  verticalReflectionLinear_involutive x

theorem verticalReflection_verticalDirection :
    verticalReflection m (verticalDirection m) = -verticalDirection m := by
  rw [verticalReflection_apply, verticalReflectionLinear_apply, last_verticalDirection, mul_one,
    two_smul]
  abel

theorem verticalReflection_mem_tiltCylinder_iff {z : Space (m + 1)} {r : ℝ} :
    verticalReflection m z ∈ tiltCylinder (verticalDirection m) r ↔
      z ∈ tiltCylinder (verticalDirection m) r := by
  rw [mem_tiltCylinder_vertical_iff, mem_tiltCylinder_vertical_iff,
    horizontal_verticalReflection, last_verticalReflection, abs_neg]

theorem preimage_verticalReflection_tiltCylinder (r : ℝ) :
    verticalReflection m ⁻¹' tiltCylinder (verticalDirection m) r =
      tiltCylinder (verticalDirection m) r := by
  ext z
  exact verticalReflection_mem_tiltCylinder_iff

theorem preimage_verticalReflection_tiltCylinder_inter (r c : ℝ) :
    verticalReflection m ⁻¹' (tiltCylinder (verticalDirection m) r ∩
      {z : Space (m + 1) | c ≤ |z (Fin.last m)|}) =
      tiltCylinder (verticalDirection m) r ∩ {z : Space (m + 1) | c ≤ |z (Fin.last m)|} := by
  ext z
  simp only [mem_preimage, mem_inter_iff, verticalReflection_mem_tiltCylinder_iff,
    mem_ofPred_eq, last_verticalReflection, abs_neg]

/-- Integrals are invariant under the vertical reflection. -/
theorem integral_comp_verticalReflection (F : Space (m + 1) → ℝ) :
    (∫ z, F (verticalReflection m z)) = ∫ z, F z :=
  (verticalReflection m).measurePreserving.integral_comp
    (verticalReflection m).toHomeomorph.measurableEmbedding F

/-- Set integrals over reflection-invariant sets are invariant under the vertical reflection. -/
theorem setIntegral_comp_verticalReflection {A : Set (Space (m + 1))}
    (hA : verticalReflection m ⁻¹' A = A) (F : Space (m + 1) → ℝ) :
    (∫ z in A, F (verticalReflection m z)) = ∫ z in A, F z := by
  have h := (verticalReflection m).measurePreserving.setIntegral_preimage_emb
    (verticalReflection m).toHomeomorph.measurableEmbedding F A
  rwa [hA] at h

/-! ## Reflected rescalings -/

section Reflected

variable (V : Space (m + 1) → ℝ) (z : Space (m + 1))

theorem gradient_comp_verticalReflection :
    gradient (fun w ↦ V (verticalReflection m w)) z =
      verticalReflection m (gradient V (verticalReflection m z)) :=
  gradient_comp_linearIsometryEquiv V (verticalReflection m) z

theorem horizontal_gradient_comp_verticalReflection :
    horizontal (gradient (fun w ↦ V (verticalReflection m w)) z) =
      horizontal (gradient V (verticalReflection m z)) := by
  rw [gradient_comp_verticalReflection, horizontal_verticalReflection]

theorem verticalDerivative_comp_verticalReflection :
    verticalDerivative (fun w ↦ V (verticalReflection m w)) z =
      -verticalDerivative V (verticalReflection m z) := by
  rw [← gradient_last_eq_verticalDerivative, ← gradient_last_eq_verticalDerivative,
    gradient_comp_verticalReflection, last_verticalReflection]

theorem norm_gradient_comp_verticalReflection :
    ‖gradient (fun w ↦ V (verticalReflection m w)) z‖ =
      ‖gradient V (verticalReflection m z)‖ := by
  rw [gradient_comp_verticalReflection, LinearIsometryEquiv.norm_map]

theorem rescaledPhaseEnergyDensity_comp_verticalReflection (f : ℝ → ℝ) (R : ℝ) :
    rescaledPhaseEnergyDensity f R (fun w ↦ V (verticalReflection m w)) z =
      rescaledPhaseEnergyDensity f R V (verticalReflection m z) := by
  simp only [rescaledPhaseEnergyDensity, indicator_apply, mem_ofPred_eq,
    norm_gradient_comp_verticalReflection]

end Reflected

theorem tiltCylinder_neg {d : ℕ} (e : Space d) (r : ℝ) :
    tiltCylinder (-e) r = tiltCylinder e r := by
  ext y
  simp only [tiltCylinder, mem_ofPred_eq, inner_neg_right, neg_smul_neg, abs_neg]

theorem cylinderTilt_neg (T : ℝ) (V : Space (m + 1) → ℝ) (r : ℝ) (e : Space (m + 1)) :
    cylinderTilt T V r (-e) = cylinderTilt T V r e := by
  unfold cylinderTilt diffuseTiltDensity
  rw [tiltCylinder_neg]
  simp only [inner_neg_right, neg_sq]

theorem cylinderTilt_comp_verticalReflection (T : ℝ) (V : Space (m + 1) → ℝ) (r : ℝ) :
    cylinderTilt T (fun w ↦ V (verticalReflection m w)) r (verticalDirection m) =
      cylinderTilt T V r (verticalDirection m) := by
  rw [cylinderTilt_comp_linearIsometryEquiv, verticalReflection_verticalDirection,
    cylinderTilt_neg]

theorem gradient_neg_fun {d : ℕ} (H : Space d → ℝ) (y : Space d) :
    gradient (fun z ↦ -H z) y = -gradient H y := by
  simp [gradient]

/-! ## Identification of the normal (HA11) -/

/-- For unit vectors `e, e'`: `⟪p, e⟫² + ⟪p, e'⟫² ≤ (1 + |⟪e, e'⟫|) ‖p‖²`. -/
theorem inner_sq_add_inner_sq_le {d : ℕ} {e e' : Space d} (he : ‖e‖ = 1) (he' : ‖e'‖ = 1)
    (p : Space d) :
    inner ℝ p e ^ 2 + inner ℝ p e' ^ 2 ≤ (1 + |inner ℝ e e'|) * ‖p‖ ^ 2 := by
  set a := inner ℝ p e
  set b := inner ℝ p e'
  set s := inner ℝ e e'
  have hq : ‖a • e + b • e'‖ ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * s := by
    rw [norm_add_sq_real, norm_smul, norm_smul, he, he', real_inner_smul_left,
      real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one, sq_abs, sq_abs]
    ring
  have hcs : a * a + b * b ≤ ‖p‖ * ‖a • e + b • e'‖ := by
    have h1 : inner ℝ p (a • e + b • e') = a * a + b * b := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [← h1]
    exact real_inner_le_norm _ _
  have hab : 2 * a * b * s ≤ |s| * (a ^ 2 + b ^ 2) := by
    have h2 : |2 * a * b| ≤ a ^ 2 + b ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
    calc 2 * a * b * s ≤ |2 * a * b * s| := le_abs_self _
      _ = |2 * a * b| * |s| := abs_mul _ _
      _ ≤ (a ^ 2 + b ^ 2) * |s| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      _ = |s| * (a ^ 2 + b ^ 2) := mul_comm _ _
  have hsq : (a ^ 2 + b ^ 2) ^ 2 ≤ ‖p‖ ^ 2 * ((1 + |s|) * (a ^ 2 + b ^ 2)) := by
    have h0 : 0 ≤ a * a + b * b := add_nonneg (mul_self_nonneg a) (mul_self_nonneg b)
    have h3 : (a * a + b * b) ^ 2 ≤ (‖p‖ * ‖a • e + b • e'‖) ^ 2 := pow_le_pow_left₀ h0 hcs 2
    rw [mul_pow, hq] at h3
    nlinarith [sq_nonneg ‖p‖]
  rcases (add_nonneg (sq_nonneg a) (sq_nonneg b)).eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · nlinarith

variable {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **HA11, identification of the normal.** Let the blow-downs
`U_j = zeroExtension g u (c j + R j • ·)` converge locally in `L¹` to the half-space
`{⟪e, ·⟫ > 0}`, and let unit vectors `e' j → e₀` be such that the diffuse tilt of `U_j` along
`e' j` on the unit ball tends to zero. Then `e₀ = ± e`: otherwise the tilts along `e` and along
`e' j` together control the kinetic mass `∫_{B₁} ε |∇U_j|²`, which would tend to zero, while the
primitive mass `∫_{B₁} |∇Φ(U_j)| ≤ 2 ∫_{B₁} ε |∇U_j|² + ¼ ∫_{B₁} e_ε(U_j)` tends to
`σ ω_m > 0`. -/
theorem RigidityHypotheses.eq_or_eq_neg_of_tilt_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    {e' : ℕ → Space (m + 1)} (he'1 : ∀ j, ‖e' j‖ = 1) {e₀ : Space (m + 1)}
    (he' : Tendsto e' atTop (𝓝 e₀))
    (htilt : Tendsto (fun j ↦ ∫ z in closedBall (0 : Space (m + 1)) 1,
      diffuseTiltDensity (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) (e' j) z) atTop
        (𝓝 0)) :
    e₀ = e ∨ e₀ = -e := by
  have he₀ : ‖e₀‖ = 1 := by
    have h1 := (continuous_norm.tendsto e₀).comp he'
    simp only [Function.comp_def, he'1] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  by_contra hne
  push Not at hne
  have hs : |inner ℝ e e₀| < 1 := by
    by_contra hge
    push Not at hge
    have h1 : |inner ℝ e₀ e| ≤ 1 := by
      have := abs_real_inner_le_norm e₀ e
      rwa [he₀, he, mul_one] at this
    rw [real_inner_comm] at hge
    have h2 : |inner ℝ e₀ e| = 1 := le_antisymm h1 hge
    have h3 : ‖e₀ - inner ℝ e₀ e • e‖ ^ 2 = 0 := by
      rw [norm_sub_inner_smul_sq he, he₀, ← sq_abs (inner ℝ e₀ e), h2]
      norm_num
    have h4 : e₀ = inner ℝ e₀ e • e :=
      sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3))
    rcases (abs_eq zero_le_one).mp h2 with h5 | h5
    · exact hne.1 (by rw [h4, h5, one_smul])
    · exact hne.2 (by rw [h4, h5, neg_one_smul])
  set κ₀ : ℝ := 1 - |inner ℝ e e₀| with hκ₀
  have hκ₀pos : 0 < κ₀ := by rw [hκ₀]; linarith
  have hclose : ∀ᶠ j in atTop, |inner ℝ e (e' j)| < 1 - κ₀ / 2 := by
    have ht : Tendsto (fun j ↦ |inner ℝ e (e' j)|) atTop (𝓝 |inner ℝ e e₀|) :=
      (tendsto_const_nhds.inner he').abs
    exact ht.eventually_lt_const (by linarith)
  obtain ⟨hΦ, hE, hT⟩ := hr.translated_energy_and_tilt_tendsto_of_halfspace_limit h hsharp c
    hR he hlocal (r := 1) one_pos
  set U : ℕ → Space (m + 1) → ℝ := fun j y ↦ zeroExtension g u (c j + R j • y) with hUdef
  have hUL : ∀ j, LocallyLipschitz (U j) := fun j ↦
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz (c j) (R j)
  have hUval : ∀ j y, U j y ∈ Icc (0 : ℝ) 1 := fun j y ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hK1 : IsCompact (closedBall (0 : Space (m + 1)) 1) := isCompact_closedBall 0 1
  have hS1 : MeasurableSet (closedBall (0 : Space (m + 1)) 1) := measurableSet_closedBall
  have hiD : ∀ j (w : Space (m + 1)), ‖w‖ = 1 →
      IntegrableOn (diffuseTiltDensity (R j) (U j) w) (closedBall 0 1) := fun j w hw ↦ by
    refine integrableOn_of_abs_le_mul_gradient_sq (hUL j) ?_ hS1 isBounded_closedBall
      (C := (R j)⁻¹) fun z _ ↦ ?_
    · unfold diffuseTiltDensity
      exact (((measurable_gradient (U j)).norm.pow_const 2).sub
        (((measurable_gradient (U j)).inner measurable_const).pow_const 2)).div_const (R j)
    · have h1 := inner_sq_le_norm_sq_of_unit (gradient (U j) z) hw
      unfold diffuseTiltDensity
      rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr h1) (hR j).le), div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (inner ℝ (gradient (U j) z) w)]) (inv_nonneg.mpr (hR j).le)
  have hiK : ∀ j, IntegrableOn (fun z ↦ (R j)⁻¹ * ‖gradient (U j) z‖ ^ 2) (closedBall 0 1) :=
    fun j ↦ (integrableOn_gradient_sq_of_locallyLipschitz (hUL j) hK1).const_mul _
  have hiE : ∀ j (T : ℝ), IntegrableOn (rescaledPhaseEnergyDensity f T (U j)) (closedBall 0 1) :=
    fun j T ↦ h.integrableOn_rescaledPhaseEnergy (hUL j) (hUval j) T hK1
  -- the kinetic mass on the unit ball tends to zero
  have hkin : Tendsto (fun j ↦ ∫ z in closedBall (0 : Space (m + 1)) 1,
      (R j)⁻¹ * ‖gradient (U j) z‖ ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun j ↦ (2 / κ₀) * ((∫ z in closedBall (0 : Space (m + 1)) 1,
        diffuseTiltDensity (R j) (U j) e z) + ∫ z in closedBall (0 : Space (m + 1)) 1,
          diffuseTiltDensity (R j) (U j) (e' j) z)) atTop (𝓝 0) := by
      have := (hT.add htilt).const_mul (2 / κ₀)
      rwa [add_zero, mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun j ↦ setIntegral_nonneg hS1 fun z _ ↦ ?_) ?_
      hlim
    · have := hR j
      positivity
    filter_upwards [hclose] with j hj
    rw [← integral_add (hiD j e he) (hiD j (e' j) (he'1 j)), ← integral_const_mul]
    refine setIntegral_mono_on (hiK j)
      (((hiD j e he).add (hiD j (e' j) (he'1 j))).const_mul _) hS1 fun z _ ↦ ?_
    have hp := inner_sq_add_inner_sq_le he (he'1 j) (gradient (U j) z)
    have hR0 := hR j
    have hRne : R j ≠ 0 := hR0.ne'
    have hκne : κ₀ ≠ 0 := hκ₀pos.ne'
    have hkey : κ₀ / 2 * ‖gradient (U j) z‖ ^ 2 ≤
        (‖gradient (U j) z‖ ^ 2 - inner ℝ (gradient (U j) z) e ^ 2) +
          (‖gradient (U j) z‖ ^ 2 - inner ℝ (gradient (U j) z) (e' j) ^ 2) := by
      nlinarith [sq_nonneg ‖gradient (U j) z‖, abs_nonneg (inner ℝ e (e' j))]
    unfold diffuseTiltDensity
    calc (R j)⁻¹ * ‖gradient (U j) z‖ ^ 2
        = 2 / κ₀ * ((κ₀ / 2 * ‖gradient (U j) z‖ ^ 2) / R j) := by
          field_simp
      _ ≤ 2 / κ₀ * (((‖gradient (U j) z‖ ^ 2 - inner ℝ (gradient (U j) z) e ^ 2) +
            (‖gradient (U j) z‖ ^ 2 - inner ℝ (gradient (U j) z) (e' j) ^ 2)) / R j) := by
          gcongr
      _ = 2 / κ₀ * ((‖gradient (U j) z‖ ^ 2 - inner ℝ (gradient (U j) z) e ^ 2) / R j +
            (‖gradient (U j) z‖ ^ 2 - inner ℝ (gradient (U j) z) (e' j) ^ 2) / R j) := by
          rw [add_div]
  -- the primitive mass is controlled by the kinetic mass and a quarter of the energy
  have hbound : ∀ j, (∫ z in closedBall (0 : Space (m + 1)) 1,
      ‖gradient (fun y ↦ phasePrimitive f (U j y)) z‖) ≤
      2 * (∫ z in closedBall (0 : Space (m + 1)) 1, (R j)⁻¹ * ‖gradient (U j) z‖ ^ 2) +
        1 / 4 * ∫ z in closedBall (0 : Space (m + 1)) 1,
          rescaledPhaseEnergyDensity f (R j) (U j) z := by
    intro j
    have hR0 := hR j
    have hR4 : 0 < R j / 4 := by positivity
    refine (hr.competitorPrimitive_gradient_integral_le_energy h (hUL j) (hUval j) hR4
      hK1).trans ?_
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hiK j).const_mul 2) ((hiE j (R j)).const_mul _)]
    refine setIntegral_mono_on (hiE j _) (((hiK j).const_mul 2).add ((hiE j (R j)).const_mul _))
      hS1 fun z _ ↦ ?_
    simp only [rescaledPhaseEnergyDensity, indicator_apply, mem_ofPred_eq]
    split_ifs with hpos
    · have h1 : ‖gradient (U j) z‖ ^ 2 / (2 * (R j / 4)) =
          2 * ((R j)⁻¹ * ‖gradient (U j) z‖ ^ 2) := by
        field_simp
        ring
      have h2 : 0 ≤ ‖gradient (U j) z‖ ^ 2 / (2 * R j) := by positivity
      rw [h1]
      linarith
    · positivity
  have hpos : 0 < phasePrimitive f 1 * ((1 : ℝ) ^ m * volume.real (closedBall (0 : Space m) 1)) := by
    have h1 := hr.phasePrimitive_one_pos h
    have h2 : 0 < volume.real (closedBall (0 : Space m) 1) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
        measure_closedBall_lt_top.ne
    positivity
  have hlimR := (hkin.const_mul 2).add (hE.const_mul (1 / 4))
  have hle := le_of_tendsto_of_tendsto' hΦ hlimR hbound
  linarith

/-- **Alignment along a subsequence (SD4 and compactness of the sphere).** For an HA11
contradiction sequence, a subsequence of the blow-downs at the free-boundary centers converges
locally in `L¹` to a half-space `{⟪e, ·⟫ > 0}` through the origin, and along it the rotated
vertical directions `Q j e_n` converge to `e` or to `-e`. -/
theorem RigidityHypotheses.exists_aligned_subseq
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ) (hx : ∀ j, x j ∈ frontier (epigraph g)) (hR : ∀ j, 0 < R j)
    (hRt : Tendsto R atTop atTop) (hδ0 : Tendsto δ atTop (𝓝 0))
    (htilt : ∀ j, cylinderTilt (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) 2
      (verticalDirection m) = δ j ^ 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ e : Space (m + 1), ‖e‖ = 1 ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x (φ j) + R (φ j) • z) -
          {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0)) ∧
      (Tendsto (fun j ↦ Q (φ j) (verticalDirection m)) atTop (𝓝 e) ∨
        Tendsto (fun j ↦ Q (φ j) (verticalDirection m)) atTop (𝓝 (-e))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hRt.eventually_ge_atTop 1)
  obtain ⟨φ₁, hφ₁, e, he, hlim₁⟩ := hr.exists_frontier_halfspace_subseq h hsharp
    (fun j ↦ x (j + N)) (fun j ↦ hx _) (R := fun j ↦ R (j + N)) (fun j ↦ hN _ (by omega))
    (hRt.comp (tendsto_add_atTop_nat N))
  have hw : ∀ j, Q (φ₁ j + N) (verticalDirection m) ∈ sphere (0 : Space (m + 1)) 1 := fun j ↦ by
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, norm_verticalDirection]
  obtain ⟨e₀, -, φ₂, hφ₂, hw₀⟩ := (isCompact_sphere (0 : Space (m + 1)) 1).tendsto_subseq hw
  set φ : ℕ → ℕ := fun j ↦ φ₁ (φ₂ j) + N with hφdef
  have hφ : StrictMono φ := fun a b hab ↦ Nat.add_lt_add_right (hφ₁ (hφ₂ hab)) N
  have hloc : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x (φ j) + R (φ j) • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0) :=
    fun K hK ↦ (hlim₁ K hK).comp hφ₂.tendsto_atTop
  have hRφ : ∀ j, 0 < R (φ j) := fun j ↦ hR (φ j)
  -- the tilt along `Q (φ j) e_n` on the unit ball tends to zero
  have htilt' : Tendsto (fun j ↦ ∫ z in closedBall (0 : Space (m + 1)) 1,
      diffuseTiltDensity (R (φ j)) (fun y ↦ zeroExtension g u (x (φ j) + R (φ j) • y))
        (Q (φ j) (verticalDirection m)) z) atTop (𝓝 0) := by
    have hlim : Tendsto (fun j ↦ (2 : ℝ) ^ m * δ (φ j) ^ 2) atTop (𝓝 0) := by
      have := ((hδ0.comp hφ.tendsto_atTop).pow 2).const_mul ((2 : ℝ) ^ m)
      rwa [zero_pow two_ne_zero, mul_zero] at this
    refine squeeze_zero (fun j ↦ setIntegral_nonneg measurableSet_closedBall fun z _ ↦
      div_nonneg (sub_nonneg.mpr (inner_sq_le_norm_sq_of_unit _ (by
        rw [LinearIsometryEquiv.norm_map, norm_verticalDirection]))) (hRφ j).le) (fun j ↦ ?_) hlim
    set V : Space (m + 1) → ℝ := fun y ↦ zeroExtension g u (x (φ j) + R (φ j) • y) with hV
    have hVL : LocallyLipschitz V :=
      locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz _ _
    have hunit : ‖Q (φ j) (verticalDirection m)‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map, norm_verticalDirection]
    have hct := htilt (φ j)
    rw [show (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) =
      fun z ↦ V (Q (φ j) z) from rfl, cylinderTilt_comp_linearIsometryEquiv] at hct
    have hcyl : (∫ z in tiltCylinder (Q (φ j) (verticalDirection m)) 2,
        diffuseTiltDensity (R (φ j)) V (Q (φ j) (verticalDirection m)) z) =
        (2 : ℝ) ^ m * δ (φ j) ^ 2 := by
      rw [← hct]
      unfold cylinderTilt
      rw [← mul_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero),
        one_mul]
    rw [← hcyl]
    refine setIntegral_mono_set ?_ ?_ (Eventually.of_forall fun z hz ↦
      mem_tiltCylinder_of_norm_lt hunit (by
        have hz' : z ∈ closedBall (0 : Space (m + 1)) 1 := hz
        rw [mem_closedBall, dist_zero_right] at hz'
        linarith))
    · refine integrableOn_of_abs_le_mul_gradient_sq hVL ?_ (isOpen_tiltCylinder _ _).measurableSet
        (isBounded_tiltCylinder hunit 2) (C := (R (φ j))⁻¹) fun z _ ↦ ?_
      · unfold diffuseTiltDensity
        exact (((measurable_gradient V).norm.pow_const 2).sub
          (((measurable_gradient V).inner measurable_const).pow_const 2)).div_const _
      · have h1 := inner_sq_le_norm_sq_of_unit (gradient V z) hunit
        unfold diffuseTiltDensity
        rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr h1) (hRφ j).le), div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left
          (by nlinarith [sq_nonneg (inner ℝ (gradient V z) (Q (φ j) (verticalDirection m)))])
          (inv_nonneg.mpr (hRφ j).le)
    · exact Eventually.of_forall fun z ↦ div_nonneg
        (sub_nonneg.mpr (inner_sq_le_norm_sq_of_unit _ hunit)) (hRφ j).le
  have hid := hr.eq_or_eq_neg_of_tilt_tendsto_zero h hsharp (fun j ↦ x (φ j)) hRφ he hloc
    (e' := fun j ↦ Q (φ j) (verticalDirection m))
    (fun j ↦ by rw [LinearIsometryEquiv.norm_map, norm_verticalDirection]) hw₀ htilt'
  refine ⟨φ, hφ, e, he, hloc, ?_⟩
  rcases hid with hid | hid
  · exact Or.inl (hid ▸ hw₀)
  · exact Or.inr (hid ▸ hw₀)

/-! ## Transfer of the HA6 integrals under the vertical reflection -/

section ReflectIntegrals

variable (V : Space (m + 1) → ℝ)

theorem setIntegral_height_comp_verticalReflection (a δ R r : ℝ) (H : Space m → ℝ) :
    (∫ z in tiltCylinder (verticalDirection m) r,
      ((z (Fin.last m) - a) / δ - H (horizontal z)) ^ 2 *
        (R⁻¹ * ‖gradient (fun w ↦ V (verticalReflection m w)) z‖ ^ 2)) =
    ∫ z in tiltCylinder (verticalDirection m) r,
      ((z (Fin.last m) - -a) / δ - -H (horizontal z)) ^ 2 * (R⁻¹ * ‖gradient V z‖ ^ 2) := by
  calc (∫ z in tiltCylinder (verticalDirection m) r,
      ((z (Fin.last m) - a) / δ - H (horizontal z)) ^ 2 *
        (R⁻¹ * ‖gradient (fun w ↦ V (verticalReflection m w)) z‖ ^ 2))
      = ∫ z in tiltCylinder (verticalDirection m) r,
          (fun w ↦ ((w (Fin.last m) - -a) / δ - -H (horizontal w)) ^ 2 *
            (R⁻¹ * ‖gradient V w‖ ^ 2)) (verticalReflection m z) := by
        refine setIntegral_congr_fun (isOpen_tiltCylinder _ _).measurableSet fun z _ ↦ ?_
        simp only [norm_gradient_comp_verticalReflection, horizontal_verticalReflection,
          last_verticalReflection]
        ring
    _ = _ := setIntegral_comp_verticalReflection (preimage_verticalReflection_tiltCylinder r)
          (fun w ↦ ((w (Fin.last m) - -a) / δ - -H (horizontal w)) ^ 2 *
            (R⁻¹ * ‖gradient V w‖ ^ 2))

theorem integral_flux_comp_verticalReflection (δ R : ℝ) (ζ : Space m → Space m) (ψ : ℝ → ℝ) :
    (∫ z, (fun t ↦ ψ (-t)) (z (Fin.last m)) * inner ℝ (ζ (horizontal z))
      ((δ⁻¹ * R⁻¹ * verticalDerivative (fun w ↦ V (verticalReflection m w)) z) •
        horizontal (gradient (fun w ↦ V (verticalReflection m w)) z))) =
    -∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z))
      ((δ⁻¹ * R⁻¹ * verticalDerivative V z) • horizontal (gradient V z)) := by
  rw [← integral_neg]
  calc (∫ z, (fun t ↦ ψ (-t)) (z (Fin.last m)) * inner ℝ (ζ (horizontal z))
      ((δ⁻¹ * R⁻¹ * verticalDerivative (fun w ↦ V (verticalReflection m w)) z) •
        horizontal (gradient (fun w ↦ V (verticalReflection m w)) z)))
      = ∫ z, (fun w ↦ -(ψ (w (Fin.last m)) * inner ℝ (ζ (horizontal w))
          ((δ⁻¹ * R⁻¹ * verticalDerivative V w) • horizontal (gradient V w))))
            (verticalReflection m z) := by
        refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
        simp only [verticalDerivative_comp_verticalReflection,
          horizontal_gradient_comp_verticalReflection, horizontal_verticalReflection,
          last_verticalReflection, real_inner_smul_right]
        ring
    _ = _ := integral_comp_verticalReflection (fun w ↦ -(ψ (w (Fin.last m)) *
          inner ℝ (ζ (horizontal w))
            ((δ⁻¹ * R⁻¹ * verticalDerivative V w) • horizontal (gradient V w))))

theorem setIntegral_energy_comp_verticalReflection (f : ℝ → ℝ) (R r c : ℝ) :
    (∫ z in tiltCylinder (verticalDirection m) r ∩ {z | c ≤ |z (Fin.last m)|},
      rescaledPhaseEnergyDensity f R (fun w ↦ V (verticalReflection m w)) z) =
    ∫ z in tiltCylinder (verticalDirection m) r ∩ {z | c ≤ |z (Fin.last m)|},
      rescaledPhaseEnergyDensity f R V z := by
  simp only [rescaledPhaseEnergyDensity_comp_verticalReflection]
  exact setIntegral_comp_verticalReflection (preimage_verticalReflection_tiltCylinder_inter r c)
    (rescaledPhaseEnergyDensity f R V)

theorem setIntegral_normal_comp_verticalReflection (R s : ℝ) (w : Space m → ℝ) :
    (∫ z in tiltCylinder (verticalDirection m) s,
      verticalDerivative (fun w ↦ V (verticalReflection m w)) z ^ 2 / R * w (horizontal z)) =
    ∫ z in tiltCylinder (verticalDirection m) s,
      verticalDerivative V z ^ 2 / R * w (horizontal z) := by
  calc (∫ z in tiltCylinder (verticalDirection m) s,
      verticalDerivative (fun w ↦ V (verticalReflection m w)) z ^ 2 / R * w (horizontal z))
      = ∫ z in tiltCylinder (verticalDirection m) s,
          (fun y ↦ verticalDerivative V y ^ 2 / R * w (horizontal y)) (verticalReflection m z) := by
        refine setIntegral_congr_fun (isOpen_tiltCylinder _ _).measurableSet fun z _ ↦ ?_
        simp only [verticalDerivative_comp_verticalReflection, horizontal_verticalReflection,
          neg_sq]
    _ = _ := setIntegral_comp_verticalReflection (preimage_verticalReflection_tiltCylinder s)
          (fun y ↦ verticalDerivative V y ^ 2 / R * w (horizontal y))

end ReflectIntegrals

theorem tsupport_comp_neg_subset_Ioo {ψ : ℝ → ℝ} {r : ℝ}
    (hψ : tsupport ψ ⊆ Ioo (-r) r) : tsupport (fun t ↦ ψ (-t)) ⊆ Ioo (-r) r := by
  have h := tsupport_comp_eq_preimage ψ (Homeomorph.neg ℝ)
  intro t ht
  have ht' : t ∈ (Homeomorph.neg ℝ) ⁻¹' tsupport ψ := by
    rw [← h]
    exact ht
  have h2 : -r < -t ∧ -t < r := hψ ht'
  exact ⟨by linarith [h2.2], by linarith [h2.1]⟩

/-! ## Aligned HA6 inputs -/

/-- The conclusion of the HA6 inputs (`HasHarmonicHeightData`) for one HA11 sequence. -/
def HarmonicHeightConclusion (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (f : ℝ → ℝ) (σ M : ℝ)
    (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ) : Prop :=
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

theorem hasHarmonicHeightData_iff {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ}
    {σ M : ℝ} : HasHarmonicHeightData g u f σ M ↔
      ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
        (δ : ℕ → ℝ),
        (∀ j, x j ∈ frontier (epigraph g)) → (∀ j, 0 < R j) → Tendsto R atTop atTop →
        (∀ j, 0 < δ j) → Tendsto δ atTop (𝓝 0) → Tendsto (fun j ↦ R j * δ j) atTop atTop →
        (∀ j, cylinderTilt (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) 2
          (verticalDirection m) = δ j ^ 2) →
        HarmonicHeightConclusion g u f σ M x R Q δ :=
  Iff.rfl

/-- The HA6 conclusion along a subsequence gives it along the sequence. -/
theorem HarmonicHeightConclusion.of_subseq {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {σ M : ℝ} {x : ℕ → Space (m + 1)} {R : ℕ → ℝ}
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)} {δ : ℕ → ℝ} {φ₀ : ℕ → ℕ}
    (hφ₀ : StrictMono φ₀)
    (hc : HarmonicHeightConclusion g u f σ M (fun j ↦ x (φ₀ j)) (fun j ↦ R (φ₀ j))
      (fun j ↦ Q (φ₀ j)) (fun j ↦ δ (φ₀ j))) :
    HarmonicHeightConclusion g u f σ M x R Q δ := by
  obtain ⟨φ, hφ, H, U, a, rest⟩ := hc
  exact ⟨fun j ↦ φ₀ (φ j), hφ₀.comp hφ, H, U, a, rest⟩

/-- The HA6 conclusion for the reflected rotations `Q j ∘ S` gives it for `Q j`, with `-H` and
`-a j` in place of `H` and `a j`. -/
theorem HarmonicHeightConclusion.of_reflect {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {σ M : ℝ} {x : ℕ → Space (m + 1)} {R : ℕ → ℝ}
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)} {δ : ℕ → ℝ}
    (hc : HarmonicHeightConclusion g u f σ M x R
      (fun j ↦ (verticalReflection m).trans (Q j)) δ) :
    HarmonicHeightConclusion g u f σ M x R Q δ := by
  obtain ⟨φ, hφ, H, U, a, hU, hBU, hH, hΔ, hM1, hM2, ha0, hI1, hI2, hI3, hI4⟩ := hc
  refine ⟨φ, hφ, fun y ↦ -H y, U, fun j ↦ -a j, hU, hBU, hH.neg, fun y hy ↦ ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · change Δ (-H) y = 0
    rw [laplacian_neg, Pi.neg_apply, hΔ y hy, neg_zero]
  · simpa only [neg_sq] using hM1
  · simpa only [gradient_neg_fun, norm_neg] using hM2
  · simpa only [neg_zero] using ha0.neg
  · refine hI1.congr fun j ↦ ?_
    exact setIntegral_height_comp_verticalReflection
      (fun w ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) w)) _ _ _ _ H
  · intro ζ hζ hζs ψ hψ hψs
    have h1 := (hI2 ζ hζ hζs (fun t ↦ ψ (-t)) (hψ.comp continuous_neg)
      (tsupport_comp_neg_subset_Ioo hψs)).neg
    have hlim : -(-(σ * (fun t ↦ ψ (-t)) 0) * ∫ y, inner ℝ (ζ y) (gradient H y)) =
        -(σ * ψ 0) * ∫ y, inner ℝ (ζ y) (gradient (fun y ↦ -H y) y) := by
      simp only [neg_zero, gradient_neg_fun, inner_neg_right, integral_neg]
      ring
    rw [hlim] at h1
    refine h1.congr fun j ↦ ?_
    exact neg_eq_iff_eq_neg.mpr (integral_flux_comp_verticalReflection
      (fun w ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) w)) _ _ ζ ψ)
  · intro c hc
    refine (hI3 c hc).congr fun j ↦ ?_
    exact congrArg _ (setIntegral_energy_comp_verticalReflection
      (fun w ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) w)) f _ _ c)
  · intro s hs w hw hw0 η hη
    filter_upwards [hI4 s hs w hw hw0 η hη] with j hj
    exact (setIntegral_normal_comp_verticalReflection
      (fun w ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) w)) _ s w).symm.le.trans hj

/-- **The HA6 inputs for aligned sequences.** As `HasHarmonicHeightData`, but only for HA11
sequences whose unrotated blow-downs converge locally in `L¹` to a half-space `{⟪e, ·⟫ > 0}`
through the origin, with `Q j e_n → e` (positive phase above the plane in the rotated frame).
This is the setting of `RigidityHypotheses.exists_normalizedHeight_limit_of_cone` and
`RigidityHypotheses.verticalPlanarLayers_of_rotated`. -/
def HasAlignedHarmonicHeightData (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (f : ℝ → ℝ)
    (σ M : ℝ) : Prop :=
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
    HarmonicHeightConclusion g u f σ M x R Q δ

/-- **Removing the alignment.** Pass to the aligned subsequence of
`RigidityHypotheses.exists_aligned_subseq`; if `Q j e_n → -e`, replace `Q j` by `Q j ∘ S`. -/
theorem RigidityHypotheses.hasHarmonicHeightData_of_aligned
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {σ M : ℝ} (hal : HasAlignedHarmonicHeightData g u f σ M) :
    HasHarmonicHeightData g u f σ M := by
  rw [hasHarmonicHeightData_iff]
  intro x R Q δ hx hR hRt hδ hδ0 hRδ htilt
  obtain ⟨φ₀, hφ₀, e, he, hloc, hor⟩ :=
    hr.exists_aligned_subseq h hsharp x R Q δ hx hR hRt hδ0 htilt
  have hx' : ∀ j, x (φ₀ j) ∈ frontier (epigraph g) := fun j ↦ hx _
  have hR' : ∀ j, 0 < R (φ₀ j) := fun j ↦ hR _
  have hRt' : Tendsto (fun j ↦ R (φ₀ j)) atTop atTop := hRt.comp hφ₀.tendsto_atTop
  have hδ' : ∀ j, 0 < δ (φ₀ j) := fun j ↦ hδ _
  have hδ0' : Tendsto (fun j ↦ δ (φ₀ j)) atTop (𝓝 0) := hδ0.comp hφ₀.tendsto_atTop
  have hRδ' : Tendsto (fun j ↦ R (φ₀ j) * δ (φ₀ j)) atTop atTop := hRδ.comp hφ₀.tendsto_atTop
  refine HarmonicHeightConclusion.of_subseq hφ₀ ?_
  rcases hor with hpos | hneg
  · exact hal _ _ _ _ e hx' hR' hRt' hδ' hδ0' hRδ' (fun j ↦ htilt _) he hloc hpos
  · refine HarmonicHeightConclusion.of_reflect ?_
    refine hal _ _ _ _ e hx' hR' hRt' hδ' hδ0' hRδ' (fun j ↦ ?_) he hloc ?_
    · have h1 := cylinderTilt_comp_verticalReflection (R (φ₀ j))
        (fun z ↦ zeroExtension g u (x (φ₀ j) + R (φ₀ j) • Q (φ₀ j) z)) 2
      rw [htilt (φ₀ j)] at h1
      exact h1
    · have h1 := hneg.neg
      rw [neg_neg] at h1
      refine h1.congr fun j ↦ ?_
      rw [LinearIsometryEquiv.trans_apply, verticalReflection_verticalDirection, map_neg]

/-- **HA0 from the aligned HA6 inputs.** -/
theorem RigidityHypotheses.hasCylinderTiltDecay_of_alignedHeightData
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {σ M : ℝ} (hσ : 0 ≤ σ) (hM : 0 ≤ M) (hal : HasAlignedHarmonicHeightData g u f σ M) :
    HasCylinderTiltDecay g u :=
  hr.hasCylinderTiltDecay_of_heightData h hσ hM (hr.hasHarmonicHeightData_of_aligned h hsharp hal)

/-! ## Energy tails off the plane (FE3 with HA8) -/

theorem abs_apply_le_norm_space {d : ℕ} (y : Space d) (k : Fin d) : |y k| ≤ ‖y‖ := by
  have h2 : ‖y k‖ ^ 2 ≤ ∑ i, ‖y i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i ↦ ‖y i‖ ^ 2) (fun i _ ↦ sq_nonneg _) (Finset.mem_univ k)
  have h3 := Real.abs_le_sqrt h2
  rw [abs_norm, ← EuclideanSpace.norm_eq] at h3
  rwa [← Real.norm_eq_abs]

theorem norm_sub_le_of_mem_closedCoordCube {d : ℕ} {x₀ x : Space d} {L : ℝ} (hL : 0 ≤ L)
    (hx : x ∈ closedCoordCube x₀ L) : ‖x - x₀‖ ≤ Real.sqrt d * L := by
  have hx' : ∀ i : Fin d, |(x - x₀) i| ≤ L := mem_closedCoordCube_iff.mp hx
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hL, ← Real.sqrt_mul (Nat.cast_nonneg d)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(x - x₀) i‖ ^ 2 ≤ ∑ _i : Fin d, L ^ 2 := Finset.sum_le_sum fun i _ ↦ by
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx' i) 2
    _ = d * L ^ 2 := by simp

theorem sub_smul_verticalDirection_last (x : Space (m + 1)) (t₀ : ℝ) :
    (x - t₀ • verticalDirection m) (Fin.last m) = x (Fin.last m) - t₀ := by
  simp [verticalDirection]

theorem sub_smul_verticalDirection_castSucc (x : Space (m + 1)) (t₀ : ℝ) (k : Fin m) :
    (x - t₀ • verticalDirection m) (Fin.castSucc k) = x (Fin.castSucc k) := by
  simp [verticalDirection, Fin.castSucc_ne_last]

/-- **FE3 tails in the aligned setting.** Along an aligned HA11 sequence, the energy of the
cylinder `Q_r` at distance at least `c > 0` from the horizontal plane is `o(δ_j²)`: below the
plane the rotated rescalings eventually vanish (HA8), and above it they eventually lie in the
stable well on a coordinate cube, where the energy is `O(R_j e^{-κ R_j})` (FE3); finally
`δ_j⁻¹ ≤ R_j` eventually. -/
theorem RigidityHypotheses.tendsto_energy_tail_of_aligned
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (x : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hRδ : Tendsto (fun j ↦ R j * δ j) atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x j + R j • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0))
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    (hQ : Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e)) {r c : ℝ} (hr0 : 0 < r)
    (hc : 0 < c) :
    Tendsto (fun j ↦ (δ j)⁻¹ ^ 2 *
      ∫ z in tiltCylinder (verticalDirection m) r ∩ {z | c ≤ |z (Fin.last m)|},
        rescaledPhaseEnergyDensity f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z)
      atTop (𝓝 0) := by
  obtain ⟨b, c₁, C, hb, hc₁, hc₁C, hW⟩ := hr.exists_stable_well_potential_bounds h
  have hV := hr.verticalPlanarLayers_of_rotated h hsharp x hR hRt he hlocal hQ
  set t₀ : ℝ := r + 3 * c / 4 with ht₀
  set L : ℝ := r + c / 4 with hL
  set x₀ : Space (m + 1) := t₀ • verticalDirection m with hx₀
  set S : ℝ := Real.sqrt (m + 1 : ℕ) * L + t₀ with hS
  set A : Set (Space (m + 1)) :=
    tiltCylinder (verticalDirection m) r ∩ {z | c ≤ |z (Fin.last m)|} with hA
  set K : ℝ := 4 * C * (m + 1 : ℝ) ^ 2 * b ^ 2 with hK
  set a₀ : ℝ := Real.sqrt c₁ * (c / 2) with ha₀
  have hC0 : 0 ≤ C := hc₁.le.trans hc₁C
  have hK0 : 0 ≤ K := by positivity
  have ha₀pos : 0 < a₀ := by positivity
  have hLpos : 0 < L := by positivity
  -- the region `A` lies in `closedBall 0 (2 r)`
  have hAball : A ⊆ closedBall (0 : Space (m + 1)) (2 * r) :=
    inter_subset_left.trans (ha6_tiltCylinder_subset_closedBall r)
  have hAfin : volume A < ⊤ := (measure_mono hAball).trans_lt measure_closedBall_lt_top
  set Vol : ℝ := volume.real (closedBall (0 : Space (m + 1)) (2 * r)) with hVol
  have hAvol : volume.real A ≤ Vol :=
    measureReal_mono hAball measure_closedBall_lt_top.ne
  -- pointwise exponential bound on `A`, eventually
  have hpt : ∀ᶠ j in atTop, ∀ z ∈ A,
      rescaledPhaseEnergyDensity f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z ≤
        K * R j * Real.exp (-2 * Real.sqrt c₁ * (c / 4) * R j) := by
    filter_upwards [hV.upper S (c / 2) b (by positivity) hb.1, hV.lower (2 * r) c hc]
      with j hup hlow
    intro z hz
    have hE0 : 0 ≤ rescaledPhaseEnergyDensity f (R j)
        (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z :=
      hr.rescaledPhaseEnergyDensity_nonneg h (hR j).le
        (fun w ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩) z
    obtain ⟨hzQ, hzc⟩ := hz
    have hzQ' := mem_tiltCylinder_vertical_iff.mp hzQ
    have hzc' : c ≤ |z (Fin.last m)| := hzc
    rcases le_abs'.mp hzc' with hneg | hpos
    · -- below the plane the rescaling vanishes, hence so does its energy
      have h0 : zeroExtension g u (x j + R j • Q j z) = 0 :=
        hlow z (ha6_tiltCylinder_subset_closedBall r hzQ) (by linarith)
      have hE : rescaledPhaseEnergyDensity f (R j)
          (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z = 0 := by
        simp only [rescaledPhaseEnergyDensity, indicator_apply, mem_ofPred_eq, h0, lt_irrefl,
          ite_false]
      rw [hE]
      exact mul_nonneg (mul_nonneg hK0 (hR j).le) (Real.exp_nonneg _)
    · -- above the plane: exponential decay in the stable well on a coordinate cube
      have hwell : ∀ w ∈ closedCoordCube x₀ L, 1 - b ≤ zeroExtension g u (x j + R j • Q j w) := by
        intro w hw
        have hw' : ∀ i : Fin (m + 1), |(w - x₀) i| ≤ L := mem_closedCoordCube_iff.mp hw
        have hwt : c / 2 ≤ w (Fin.last m) := by
          have h1 := hw' (Fin.last m)
          rw [hx₀, sub_smul_verticalDirection_last] at h1
          have h2 := (abs_le.mp h1).1
          rw [ht₀, hL] at h2
          linarith
        have hwS : w ∈ closedBall (0 : Space (m + 1)) S := by
          rw [mem_closedBall, dist_zero_right]
          have h1 := norm_sub_le_of_mem_closedCoordCube hLpos.le hw
          have h2 : ‖x₀‖ = t₀ := by
            rw [hx₀, norm_smul, norm_verticalDirection, mul_one, Real.norm_eq_abs,
              abs_of_nonneg (by positivity)]
          calc ‖w‖ = ‖(w - x₀) + x₀‖ := by rw [sub_add_cancel]
            _ ≤ ‖w - x₀‖ + ‖x₀‖ := norm_add_le _ _
            _ ≤ S := by rw [h2, hS]; linarith
        exact (hup w hwS hwt).le
      have hzcube' : ∀ i : Fin (m + 1), |(z - x₀) i| ≤ L - c / 4 := by
        intro i
        have hLr : L - c / 4 = r := by rw [hL]; ring
        rw [hLr, hx₀]
        refine Fin.lastCases ?_ (fun k ↦ ?_) i
        · rw [sub_smul_verticalDirection_last, abs_le]
          constructor
          · rw [ht₀]; linarith
          · rw [ht₀]; linarith [le_abs_self (z (Fin.last m))]
        · rw [sub_smul_verticalDirection_castSucc]
          have h1 := abs_apply_le_norm_space (horizontal z) k
          have h2 : (horizontal z) k = z (Fin.castSucc k) := rfl
          rw [h2] at h1
          linarith
      have hzcube : z ∈ closedCoordCube x₀ (L - c / 4) := mem_closedCoordCube_iff.mpr hzcube'
      have htail := hr.rescaled_stable_well_exponential_tail h hb hc₁
        (fun s hs ↦ (hW s hs).1) (fun s hs ↦ (hW s hs).2.2.2) (x j) (hR j) (Q j) x₀
        (L := L) (d_margin := c / 4) (by positivity) (by rw [hL]; linarith) hwell z hzcube
      exact htail.2.2
  -- `δ_j⁻¹ ≤ R_j` eventually
  have hδR : ∀ᶠ j in atTop, (δ j)⁻¹ ≤ R j := by
    filter_upwards [hRδ.eventually_ge_atTop 1] with j hj
    rw [inv_le_iff_one_le_mul₀ (hδ j)]
    linarith [mul_comm (R j) (δ j)]
  have hlim : Tendsto (fun j ↦ K * Vol * (R j ^ 3 * Real.exp (-a₀ * R j))) atTop (𝓝 0) := by
    have := ((tendsto_pow_mul_exp_neg_atTop_zero 3 ha₀pos).comp hRt).const_mul (K * Vol)
    rwa [mul_zero] at this
  refine squeeze_zero' (Eventually.of_forall fun j ↦ mul_nonneg (sq_nonneg _)
    (setIntegral_nonneg ((isOpen_tiltCylinder _ _).measurableSet.inter
      (isClosed_le continuous_const (continuous_abs.comp continuous_last)).measurableSet)
      fun z _ ↦ hr.rescaledPhaseEnergyDensity_nonneg h (hR j).le
        (fun w ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩) z)) ?_ hlim
  filter_upwards [hpt, hδR] with j hj hjδ
  have hRj := hR j
  have hint : (∫ z in A, rescaledPhaseEnergyDensity f (R j)
      (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z) ≤
      K * R j * Real.exp (-2 * Real.sqrt c₁ * (c / 4) * R j) * Vol := by
    have h1 := norm_setIntegral_le_of_norm_le_const hAfin (fun z hz ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hr.rescaledPhaseEnergyDensity_nonneg h (hR j).le
        (fun w ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩) z)]
      exact hj z hz)
    have h2 := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans h1)
    refine h2.trans (mul_le_mul_of_nonneg_left hAvol (by positivity))
  have hexp : Real.exp (-2 * Real.sqrt c₁ * (c / 4) * R j) = Real.exp (-a₀ * R j) := by
    congr 1
    rw [ha₀]
    ring
  rw [hexp] at hint
  have hδ2 : (δ j)⁻¹ ^ 2 ≤ R j ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (hδ j).le) hjδ 2
  calc (δ j)⁻¹ ^ 2 * (∫ z in A, rescaledPhaseEnergyDensity f (R j)
        (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z)
      ≤ R j ^ 2 * (K * R j * Real.exp (-a₀ * R j) * Vol) := by
        refine mul_le_mul hδ2 hint (setIntegral_nonneg ((isOpen_tiltCylinder _ _).measurableSet.inter
          (isClosed_le continuous_const (continuous_abs.comp continuous_last)).measurableSet)
          fun z _ ↦ hr.rescaledPhaseEnergyDensity_nonneg h (hR j).le
            (fun w ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩) z) (by positivity)
    _ = K * Vol * (R j ^ 3 * Real.exp (-a₀ * R j)) := by ring

/-! ## The remaining inputs for aligned sequences -/

/-- The HA6 conclusion for one HA11 sequence without the energy tails (proved for aligned
sequences by `RigidityHypotheses.tendsto_energy_tail_of_aligned`) and without the normal kinetic
bound (stated separately in `HasAlignedNormalKineticBound`): a subsequence `φ`, a `C²` function
`H` harmonic on an open `U ⊇ B̄_{1/2}` with `L²` and Dirichlet bounds `M`, and centers `a j → 0`,
such that

* **(HA6.1)** `∫_{Q_{1/2}} ((t - a_j)/δ_j - H(y))² ε |∇v_j|² → 0`;
* **(HA4)** `∫ ψ(t) ⟪ζ(y), ε ∂ₜ v_j ∇_y v_j / δ_j⟫ → -σ ψ(0) ∫ ⟪ζ, ∇H⟫` for continuous `ζ`, `ψ`
  supported in `B_{1/2}` and `(-1/2, 1/2)`. -/
def HarmonicLayerConclusion (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (σ M : ℝ)
    (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ) : Prop :=
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
    ∀ ζ : Space m → Space m, Continuous ζ → tsupport ζ ⊆ ball (0 : Space m) (1 / 2) →
      ∀ ψ : ℝ → ℝ, Continuous ψ → tsupport ψ ⊆ Ioo (-(1 / 2)) (1 / 2) →
      Tendsto (fun j ↦ ∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z))
        (((δ (φ j))⁻¹ * (R (φ j))⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u
            (x (φ j) + R (φ j) • Q (φ j) z)) z) •
          horizontal (gradient (fun z ↦ zeroExtension g u
            (x (φ j) + R (φ j) • Q (φ j) z)) z))) atTop
        (𝓝 (-(σ * ψ 0) * ∫ y, inner ℝ (ζ y) (gradient H y)))

/-- **The remaining HA4/HA6.1 inputs.** `HarmonicLayerConclusion` along every aligned HA11
sequence: free-boundary centers, `R j → ∞`, `δ j → 0`, `R j δ j → ∞`, vertical cylinder tilt
`𝓔(2, e_n) = δ j²`, blow-downs converging locally in `L¹` to `{⟪e, ·⟫ > 0}` and `Q j e_n → e`. -/
def HasAlignedHarmonicLayerData (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (σ M : ℝ) : Prop :=
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
    HarmonicLayerConclusion g u σ M x R Q δ

/-- **The normal kinetic input (ν)** (proved in `SerrinEpigraph.DiffuseNormalKinetic`,
`RigidityHypotheses.hasAlignedNormalKineticBound`). Along every aligned planar blow-down sequence
(free-boundary centers, `R j → ∞`, blow-downs converging locally in `L¹` to `{⟪e, ·⟫ > 0}`,
`Q j e_n → e`), the normal kinetic mass of the rotated rescalings in a vertical cylinder `Q_s`,
weighted by a continuous `w(y) ≥ 0`, is asymptotically at most `σ ∫_{B_s} w`: the normal kinetic
measures `ε (∂ₜ v_j)² dz` concentrate on the plane with density at most `σ` (blueprint HA6,
`ν_j ⇀ σ 𝓗ᵐ⌊{t = 0}`). -/
def HasAlignedNormalKineticBound (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (σ : ℝ) : Prop :=
  ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (e : Space (m + 1)),
    (∀ j, x j ∈ frontier (epigraph g)) → (∀ j, 0 < R j) → Tendsto R atTop atTop →
    ‖e‖ = 1 →
    (∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x j + R j • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0)) →
    Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e) →
    ∀ s ∈ Ioc (0 : ℝ) (1 / 2), ∀ w : Space m → ℝ, Continuous w → (∀ y, 0 ≤ w y) →
      ∀ η > 0, ∀ᶠ j in atTop,
        (∫ z in tiltCylinder (verticalDirection m) s,
          verticalDerivative (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z ^ 2 /
            R j * w (horizontal z)) ≤ σ * (∫ y in ball (0 : Space m) s, w y) + η

/-- The energy tails are automatic for aligned sequences; with the normal kinetic bound this
gives the aligned HA6 inputs. -/
theorem RigidityHypotheses.hasAlignedHarmonicHeightData_of_layerData
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {σ M : ℝ} (hal : HasAlignedHarmonicLayerData g u σ M)
    (hnu : HasAlignedNormalKineticBound g u σ) :
    HasAlignedHarmonicHeightData g u f σ M := by
  intro x R Q δ e hx hR hRt hδ hδ0 hRδ htilt he hloc hQ
  obtain ⟨φ, hφ, H, U, a, hU, hBU, hH, hΔ, hM1, hM2, ha0, hI1, hI2⟩ :=
    hal x R Q δ e hx hR hRt hδ hδ0 hRδ htilt he hloc hQ
  refine ⟨φ, hφ, H, U, a, hU, hBU, hH, hΔ, hM1, hM2, ha0, hI1, hI2, fun c hc ↦ ?_,
    fun s hs w hw hw0 η hη ↦ ?_⟩
  · exact (hr.tendsto_energy_tail_of_aligned h hsharp x hR hRt hδ hRδ he hloc hQ
      (by norm_num : (0 : ℝ) < 1 / 2) hc).comp hφ.tendsto_atTop
  · exact hφ.tendsto_atTop.eventually (hnu x R Q e hx hR hRt he hloc hQ s hs w hw hw0 η hη)

/-- **HA0 (`HasCylinderTiltDecay`) from the remaining inputs.** Under the hypotheses of
`RigidityHypotheses.hasCylinderTiltDecay_of_sharp_energy`, the HA0 cylinder tilt decay follows
from the HA4/HA6.1 inputs `HasAlignedHarmonicLayerData g u σ M` (some `M ≥ 0`) and the normal
kinetic bound `HasAlignedNormalKineticBound g u σ`, with `σ = phasePrimitive f 1`: HA11
alignment and FE3 tails (this module), HA6 (`SerrinEpigraph.DiffuseHarmonicApproximation`), HA7
and the HA11 contradiction argument (`SerrinEpigraph.DiffuseTiltDecay`). -/
theorem RigidityHypotheses.hasCylinderTiltDecay_of_alignedLayerData
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {M : ℝ} (hM : 0 ≤ M) (hal : HasAlignedHarmonicLayerData g u (phasePrimitive f 1) M)
    (hnu : HasAlignedNormalKineticBound g u (phasePrimitive f 1)) :
    HasCylinderTiltDecay g u :=
  hr.hasCylinderTiltDecay_of_alignedHeightData h hsharp (hr.phasePrimitive_one_pos h).le hM
    (hr.hasAlignedHarmonicHeightData_of_layerData h hsharp hal hnu)

end SerrinEpigraph
