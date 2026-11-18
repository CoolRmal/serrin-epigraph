module

public import SerrinEpigraph.SharpPlaneDensity
public import SerrinEpigraph.TiltIteration

/-!
# Uniform initial tilt smallness and kinetic mass at free-boundary centers (SD4, MC5)

Under the sharp all-center planar energy bound (SD1), this module proves the two uniform inputs
of the tilt iteration in `docs/rigidity-proof/iteration-and-directions.md`:
- **SD4 (initial smallness)**: for every `δ > 0` there is `R₀` such that
  `optimalBallTilt (zeroExtension g u) x r ≤ δ` for all free-boundary centers `x` and all
  `r ≥ R₀` (`RigidityHypotheses.exists_uniform_optimalBallTilt_le`);
- **MC5 (kinetic mass)**: there are `0 < c ≤ C` and `R_k` such that
  `c r ^ m ≤ ∫_{B_r(x)} ‖∇v‖ ^ 2 ≤ C r ^ m` for all free-boundary centers `x` and all `r ≥ R_k`
  (`RigidityHypotheses.exists_uniform_kinetic_mass_bounds`).

Both are proved by contradiction with the moving-center halfspace compactness of
`SharpPlaneDensity.lean`. For the kinetic lower bound, the primitive gradient mass of the
rescaled functions converges to the planar mass, while an unbalanced Young inequality bounds it
by the vanishing normalized kinetic mass plus half of the planar mass.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- The scale-normalized physical ball tilt equals the unit-scale diffuse tilt of the translated
dilation. -/
theorem normalized_ballTiltIntegral_eq_diffuse {m : ℕ} (v : Space (m + 1) → ℝ)
    (c e : Space (m + 1)) {R : ℝ} (hR : 0 < R) :
    R ^ (-(m : ℤ)) * ballTiltIntegral v c e R =
      ∫ z in closedBall 0 1, diffuseTiltDensity R (fun y ↦ v (c + R • y)) e z := by
  have hs := scaled_integral_diffuseTiltDensity_eq v c e (ρ := 1) hR
  simpa only [one_zpow, one_mul, mul_one] using hs.symm

/-- Normalized kinetic mass of a translated dilation on the unit ball. -/
theorem integral_norm_gradient_translate_dilation_sq_div {m : ℕ} (v : Space (m + 1) → ℝ)
    (c : Space (m + 1)) {T : ℝ} (hT : 0 < T) (r : ℝ) :
    (∫ y in closedBall 0 r, ‖gradient (fun z ↦ v (c + T • z)) y‖ ^ 2 / T) =
      (T ^ m)⁻¹ * ∫ y in closedBall c (T * r), ‖gradient v y‖ ^ 2 := by
  have heq : (fun y ↦ ‖gradient (fun z ↦ v (c + T • z)) y‖ ^ 2 / T) =
      fun y ↦ T * ‖gradient v (c + T • y)‖ ^ 2 := by
    funext y
    rw [gradient_comp_translate_dilation, norm_smul, Real.norm_of_nonneg hT.le, mul_pow]
    field_simp
  rw [heq]
  exact setIntegral_closedBall_translate_dilation_weighted (fun y ↦ ‖gradient v y‖ ^ 2) c hT r

/-- Unbalanced Young inequality for the rescaled energy: halving the scale costs the full
normalized kinetic density plus half of the original energy. -/
theorem rescaledPhaseEnergyDensity_half_scale_le {d : ℕ} (f : ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    {w : Space d → ℝ} (hW : ∀ y, 0 < w y → 0 ≤ normalizedPotential f (w y)) (y : Space d) :
    rescaledPhaseEnergyDensity f (T / 2) w y ≤
      ‖gradient w y‖ ^ 2 / T + (1 / 2) * rescaledPhaseEnergyDensity f T w y := by
  by_cases hy : 0 < w y
  · have hmem : y ∈ {x | 0 < w x} := hy
    simp only [rescaledPhaseEnergyDensity, indicator_of_mem hmem]
    have hW' := hW y hy
    have h1 : ‖gradient w y‖ ^ 2 / (2 * (T / 2)) = ‖gradient w y‖ ^ 2 / T := by
      congr 1
      ring
    have h2 : 0 ≤ ‖gradient w y‖ ^ 2 / (2 * T) := by positivity
    rw [h1]
    nlinarith
  · have hmem : y ∉ {x | 0 < w x} := hy
    simp only [rescaledPhaseEnergyDensity, indicator_of_notMem hmem, mul_zero, add_zero]
    positivity

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The full kinetic density of the zero extension is at most twice its phase energy density. -/
theorem RigidityHypotheses.norm_gradient_zeroExtension_sq_le_two_mul_phaseEnergy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    ‖gradient (zeroExtension g u) x‖ ^ 2 ≤
      2 * phaseEnergyDensity f 0 (zeroExtension g u) x := by
  by_cases hx : x ∈ epigraph g
  · have hp : x ∈ {y | 0 < zeroExtension g u y} := (h.zeroExtension_pos_iff x).mpr hx
    have hW := hr.normalizedPotential_nonneg h
      ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩
    rw [phaseEnergyDensity, indicator_of_mem hp]
    nlinarith
  · have hp : x ∉ {y | 0 < zeroExtension g u y} := by
      change ¬0 < zeroExtension g u x
      rw [zeroExtension_of_notMem hx]
      exact lt_irrefl 0
    rw [phaseEnergyDensity, indicator_of_notMem hp, h.gradient_zeroExtension_of_notMem hx,
      norm_zero]
    norm_num

/-- The sharp all-center planar energy bound controls the physical kinetic mass of every ball. -/
theorem RigidityHypotheses.kinetic_closedBall_le_of_sharp
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (x : Space (m + 1)) {r : ℝ} (hr0 : 0 < r) :
    (∫ y in closedBall x r, ‖gradient (zeroExtension g u) y‖ ^ 2) ≤
      (2 * (phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1))) * r ^ m := by
  have hK := isCompact_closedBall x r
  have hi1 := integrableOn_gradient_sq_of_locallyLipschitz h.zeroExtension_locallyLipschitz hK
  have hi2 := hr.integrableOn_phaseEnergy_zeroExtension h 0 hK
  calc (∫ y in closedBall x r, ‖gradient (zeroExtension g u) y‖ ^ 2)
      ≤ ∫ y in closedBall x r, 2 * phaseEnergyDensity f 0 (zeroExtension g u) y :=
        integral_mono hi1 (hi2.const_mul 2)
          (hr.norm_gradient_zeroExtension_sq_le_two_mul_phaseEnergy h)
    _ = 2 * ∫ y in closedBall x r, phaseEnergyDensity f 0 (zeroExtension g u) y :=
        integral_const_mul _ _
    _ ≤ 2 * (phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * r ^ m) :=
        mul_le_mul_of_nonneg_left (hsharp x r hr0) (by norm_num)
    _ = (2 * (phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1))) * r ^ m := by ring

/-- The planar mass `σ ω_m` is positive. -/
theorem RigidityHypotheses.planarMass_pos (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    0 < phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) := by
  refine mul_pos (hr.phasePrimitive_one_pos h) ?_
  exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
    measure_closedBall_lt_top.ne

/-- A sequence of radii with `n + 1 ≤ R n` is at least one and diverges. -/
theorem one_le_and_tendsto_of_succ_le {R : ℕ → ℝ} (hR : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) :
    (∀ n, 1 ≤ R n) ∧ Tendsto R atTop atTop := by
  refine ⟨fun n ↦ le_trans ?_ (hR n), ?_⟩
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · exact tendsto_atTop_mono hR
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- **SD4 initial smallness.** Under the sharp all-center planar energy bound, the optimal ball
tilt is uniformly small at all free-boundary centers and all sufficiently large radii. -/
theorem RigidityHypotheses.exists_uniform_optimalBallTilt_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ x ∈ frontier (epigraph g), ∀ r, R₀ ≤ r →
      optimalBallTilt (zeroExtension g u) x r ≤ δ := by
  by_contra hcon
  push Not at hcon
  have hseq (n : ℕ) : ∃ x ∈ frontier (epigraph g), ∃ r : ℝ, (n : ℝ) + 1 ≤ r ∧
      δ < optimalBallTilt (zeroExtension g u) x r := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact hcon ((n : ℝ) + 1) (by linarith)
  choose c hc R hRn hbig using hseq
  obtain ⟨hR1, hRt⟩ := one_le_and_tendsto_of_succ_le hRn
  obtain ⟨φ, -, e, he, hlocal⟩ := hr.exists_frontier_halfspace_subseq h hsharp c hc hR1 hRt
  have hRpos : ∀ j, 0 < R (φ j) := fun j ↦ zero_lt_one.trans_le (hR1 (φ j))
  have htilt := (hr.translated_energy_and_tilt_tendsto_of_halfspace_limit h hsharp
    (fun j ↦ c (φ j)) hRpos he hlocal one_pos).2.2
  obtain ⟨j, hj⟩ := (htilt.eventually (gt_mem_nhds hδ)).exists
  have hle := optimalBallTilt_le h.zeroExtension_locallyLipschitz (c (φ j)) (hRpos j) he
  rw [normalized_ballTiltIntegral_eq_diffuse _ (c (φ j)) e (hRpos j)] at hle
  exact lt_irrefl _ (((hbig (φ j)).trans_le hle).trans hj)

/-- The primitive gradient mass of a translated dilation on the unit ball is bounded by its
normalized kinetic mass plus half of the planar mass. -/
theorem RigidityHypotheses.primitive_mass_le_kinetic_add_half
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (c : Space (m + 1)) {T : ℝ} (hT : 0 < T) :
    (∫ x in closedBall 0 1,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + T • y))) x‖) ≤
      (T ^ m)⁻¹ * (∫ y in closedBall c T, ‖gradient (zeroExtension g u) y‖ ^ 2) +
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) / 2 := by
  let w : Space (m + 1) → ℝ := fun y ↦ zeroExtension g u (c + T • y)
  have hw : LocallyLipschitz w :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz c T
  have hwv : ∀ y, w y ∈ Icc (0 : ℝ) 1 :=
    fun y ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hK := isCompact_closedBall (0 : Space (m + 1)) 1
  have h1 := hr.competitorPrimitive_gradient_integral_le_energy h hw hwv (half_pos hT) hK
  have hi1 := h.integrableOn_rescaledPhaseEnergy hw hwv (T / 2) hK
  have hi2 : IntegrableOn (fun y ↦ ‖gradient w y‖ ^ 2 / T) (closedBall 0 1) :=
    (integrableOn_gradient_sq_of_locallyLipschitz hw hK).div_const _
  have hi3 := h.integrableOn_rescaledPhaseEnergy hw hwv T hK
  have h2 : (∫ y in closedBall 0 1, rescaledPhaseEnergyDensity f (T / 2) w y) ≤
      ∫ y in closedBall 0 1,
        (‖gradient w y‖ ^ 2 / T + (1 / 2) * rescaledPhaseEnergyDensity f T w y) :=
    integral_mono hi1 (hi2.add (hi3.const_mul _)) fun y ↦
      rescaledPhaseEnergyDensity_half_scale_le f hT
        (fun y _ ↦ hr.normalizedPotential_nonneg h (hwv y)) y
  rw [integral_add hi2 (hi3.const_mul _), integral_const_mul,
    integral_norm_gradient_translate_dilation_sq_div _ c hT 1, mul_one] at h2
  have h3 := hr.translated_rescaled_energy_le_surface_bound h hsharp c hT one_pos
  rw [one_pow, mul_one] at h3
  have h3' : (1 / 2) * (∫ y in closedBall 0 1, rescaledPhaseEnergyDensity f T w y) ≤
      (1 / 2) * (phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1)) :=
    mul_le_mul_of_nonneg_left h3 (by norm_num)
  calc (∫ x in closedBall 0 1,
        ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + T • y))) x‖)
      ≤ ∫ y in closedBall 0 1, rescaledPhaseEnergyDensity f (T / 2) w y := h1
    _ ≤ _ := h2
    _ ≤ _ := by linarith

/-- **MC5 lower bound.** Under the sharp all-center planar energy bound, the physical kinetic
mass has a uniform surface-order lower bound at every free-boundary center and large radius. -/
theorem RigidityHypotheses.exists_uniform_kinetic_mass_lower_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    ∃ c_kin R_k : ℝ, 0 < c_kin ∧ 1 ≤ R_k ∧ ∀ x ∈ frontier (epigraph g), ∀ r, R_k ≤ r →
      c_kin * r ^ m ≤ ∫ y in closedBall x r, ‖gradient (zeroExtension g u) y‖ ^ 2 := by
  by_contra hcon
  push Not at hcon
  have hseq (n : ℕ) : ∃ x ∈ frontier (epigraph g), ∃ r : ℝ, (n : ℝ) + 1 ≤ r ∧
      (∫ y in closedBall x r, ‖gradient (zeroExtension g u) y‖ ^ 2) <
        (1 / ((n : ℝ) + 1)) * r ^ m := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact hcon _ _ (by positivity) (by linarith)
  choose c hc R hRn hsmall using hseq
  obtain ⟨hR1, hRt⟩ := one_le_and_tendsto_of_succ_le hRn
  obtain ⟨φ, hφ, e, he, hlocal⟩ := hr.exists_frontier_halfspace_subseq h hsharp c hc hR1 hRt
  have hRpos : ∀ j, 0 < R (φ j) := fun j ↦ zero_lt_one.trans_le (hR1 (φ j))
  have hmass := (hr.translated_energy_and_tilt_tendsto_of_halfspace_limit h hsharp
    (fun j ↦ c (φ j)) hRpos he hlocal one_pos).1
  let k : ℕ → ℝ := fun j ↦ (R (φ j) ^ m)⁻¹ *
    ∫ y in closedBall (c (φ j)) (R (φ j)), ‖gradient (zeroExtension g u) y‖ ^ 2
  have hk : Tendsto k atTop (𝓝 0) := by
    have hupper : Tendsto (fun j ↦ 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    refine squeeze_zero (fun j ↦ mul_nonneg (inv_nonneg.mpr (pow_nonneg (hRpos j).le m))
      (integral_nonneg fun _ ↦ sq_nonneg _)) (fun j ↦ ?_) hupper
    have hs := hsmall (φ j)
    have hRm : 0 < R (φ j) ^ m := pow_pos (hRpos j) m
    change (R (φ j) ^ m)⁻¹ *
        (∫ y in closedBall (c (φ j)) (R (φ j)), ‖gradient (zeroExtension g u) y‖ ^ 2) ≤
      1 / ((φ j : ℝ) + 1)
    rw [inv_mul_le_iff₀ hRm]
    linarith [mul_comm (R (φ j) ^ m) (1 / ((φ j : ℝ) + 1))]
  have hbound (j : ℕ) :
      (∫ x in closedBall 0 1, ‖gradient (fun y ↦ phasePrimitive f
        (zeroExtension g u (c (φ j) + R (φ j) • y))) x‖) ≤
        k j + phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) / 2 :=
    hr.primitive_mass_le_kinetic_add_half h hsharp (c (φ j)) (hRpos j)
  have hlim := le_of_tendsto_of_tendsto' hmass (hk.add tendsto_const_nhds) hbound
  rw [one_pow, one_mul, zero_add] at hlim
  have hpos := hr.planarMass_pos h
  linarith

/-- **MC5.** Uniform two-sided kinetic mass bounds at all free-boundary centers. -/
theorem RigidityHypotheses.exists_uniform_kinetic_mass_bounds
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    ∃ c_kin C_kin R_k : ℝ, 0 < c_kin ∧ 0 < C_kin ∧ 1 ≤ R_k ∧
      ∀ x ∈ frontier (epigraph g), ∀ r, R_k ≤ r →
        c_kin * r ^ m ≤ (∫ y in closedBall x r, ‖gradient (zeroExtension g u) y‖ ^ 2) ∧
          (∫ y in closedBall x r, ‖gradient (zeroExtension g u) y‖ ^ 2) ≤ C_kin * r ^ m := by
  obtain ⟨c_kin, R_k, hc, hR_k, hlow⟩ := hr.exists_uniform_kinetic_mass_lower_bound h hsharp
  refine ⟨c_kin, 2 * (phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1)), R_k, hc,
    by linarith [hr.planarMass_pos h], hR_k, fun x hx r hr' ↦ ⟨hlow x hx r hr', ?_⟩⟩
  exact hr.kinetic_closedBall_le_of_sharp h hsharp x (by linarith)

end SerrinEpigraph
