module

public import SerrinEpigraph.UniformKineticMass
public import SerrinEpigraph.EventualTranslationOrder

/-!
# A uniform boundary coarse cone from one halfspace blow-down and tilt improvement

This module assembles the proof of the flatness-transfer obligation
`RigidityHypotheses.exists_uniformBoundaryCoarseCone_of_halfspace_limit` from the local tilt
improvement (blueprint `harmonic-approximation.md` HA0–HA12), which is taken here as the explicit
hypothesis `HasBallTiltImprovement (zeroExtension g u) (frontier (epigraph g))`.

* `HasBallTiltImprovement v S`: the stopped tilt-improvement recursion I2b.1 at the centers `S`,
  in exactly the form consumed by `optimalBallTilt_le_div_sq`.
* I2b–I3 and I5–I7: with the SD4 initial smallness and the MC5 kinetic mass bounds
  (`UniformKineticMass.lean`), the iteration gives `optimalBallTilt ≤ B / r ^ 2` uniformly, and
  `exists_common_limiting_lineProjection` gives one unoriented direction `e₀` with
  `ballTiltIntegral v x e₀ r ≤ D r ^ (m - 2)` at all free-boundary centers.
* DS1: every free-boundary blow-down limit (a halfspace through the origin by
  `SharpPlaneDensity.lean`) has normal `±e₀`; the sign of the antipodal difference
  `v (p + r • e₀) - v (p - r • e₀)` is bounded away from zero for large `r` and constant along the
  connected parameter set `(boundary point, radius)`, which fixes one orientation `eo`. Uniform
  one-sided convergence of every limit with normal `eo` then gives
  `HasUniformBoundaryCoarseCone g eo`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- **Uniform stopped tilt improvement** at the centers `S` (blueprint HA12 in the form I2b.1):
there are `0 < ρ < 1`, `0 ≤ q < 1`, `C ≥ 0`, a smallness threshold `δ₀ > 0`, and a starting
radius `R₁ > 0` such that at every center `x ∈ S` and every parent radius `R` with `R₁ ≤ ρ R`
whose optimal tilt is at most `δ₀`,
`optimalBallTilt v x (ρ R) ≤ q * optimalBallTilt v x R + C / (ρ R) ^ 2`. -/
def HasBallTiltImprovement {m : ℕ} (v : Space (m + 1) → ℝ) (S : Set (Space (m + 1))) : Prop :=
  ∃ ρ q C δ₀ R₁ : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧ 0 < δ₀ ∧ 0 < R₁ ∧
    ∀ x ∈ S, ∀ R : ℝ, R₁ ≤ ρ * R → optimalBallTilt v x R ≤ δ₀ →
      optimalBallTilt v x (ρ * R) ≤ q * optimalBallTilt v x R + C / (ρ * R) ^ 2

/-- Every free-boundary-centered family of diverging dilations of the zero extension has a
subsequence converging locally in `L¹` to the halfspace with inner normal `e`. -/
def HasFrontierHalfspaceLimits {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (e : Space (m + 1)) : Prop :=
  ∀ c : ℕ → Space (m + 1), (∀ j, c j ∈ frontier (epigraph g)) →
    ∀ R : ℕ → ℝ, (∀ j, 1 ≤ R j) → Tendsto R atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c (φ j) + R (φ j) • x) -
          {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)

/-- A continuous real function whose absolute value stays at least `a > 0` on a preconnected set
keeps one sign there. -/
theorem forall_le_or_forall_le_neg_of_le_abs {X : Type*} [TopologicalSpace X] {T : Set X}
    (hT : IsPreconnected T) {F : X → ℝ} (hF : ContinuousOn F T) {a : ℝ} (ha : 0 < a)
    (habs : ∀ t ∈ T, a ≤ |F t|) :
    (∀ t ∈ T, a ≤ F t) ∨ (∀ t ∈ T, F t ≤ -a) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨t₁, ht₁, h₁⟩, ⟨t₂, ht₂, h₂⟩⟩ := hcon
  have h₁' : F t₁ ≤ -a := by
    rcases le_abs'.mp (habs t₁ ht₁) with hh | hh
    · exact hh
    · linarith
  have h₂' : a ≤ F t₂ := by
    rcases le_abs'.mp (habs t₂ ht₂) with hh | hh
    · linarith
    · exact hh
  obtain ⟨t, ht, hFt⟩ := hT.intermediate_value ht₁ ht₂ hF
    (show (0 : ℝ) ∈ Icc (F t₁) (F t₂) from ⟨by linarith, by linarith⟩)
  have h0 := habs t ht
  rw [hFt, abs_zero] at h0
  linarith

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ## I2b–I3, I5–I7. Iteration and a common unoriented direction -/

/-- **I2b–I3.** Tilt improvement together with the SD4 initial smallness gives the uniform decay
`optimalBallTilt ≤ B / r ^ 2` at all free-boundary centers. -/
theorem RigidityHypotheses.exists_uniform_tilt_decay_of_tiltImprovement
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (himp : HasBallTiltImprovement (zeroExtension g u) (frontier (epigraph g))) :
    ∃ B R₀ : ℝ, 0 ≤ B ∧ 1 ≤ R₀ ∧ ∀ x ∈ frontier (epigraph g), ∀ r, R₀ ≤ r →
      optimalBallTilt (zeroExtension g u) x r ≤ B / r ^ 2 := by
  obtain ⟨ρ, q, C, δ₀, R₁, hρ0, hρ1, hq0, hq1, hC, hδ₀, -, hstep⟩ := himp
  obtain ⟨R_i, hR_i, hsmall⟩ := hr.exists_uniform_optimalBallTilt_le h hsharp hδ₀
  have hρ2 : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
  have hden : 0 < 1 - q * ρ ^ 2 := by nlinarith
  have hR₀ : 1 ≤ max R_i R₁ := le_max_of_le_left hR_i
  refine ⟨C / (1 - q * ρ ^ 2), max R_i R₁, div_nonneg hC hden.le, hR₀, fun x hx ↦ ?_⟩
  refine optimalBallTilt_le_div_sq h.zeroExtension_locallyLipschitz x hρ0 hρ1 hq0 hq1 hC
    hδ₀.le (by linarith) (fun r hr' ↦ hsmall x hx r ((le_max_left _ _).trans hr')) ?_
  intro R hR
  have hRpos : 0 < R :=
    pos_of_mul_pos_right ((by linarith : (0 : ℝ) < max R_i R₁).trans_le hR) hρ0.le
  have hρR : ρ * R ≤ R := mul_le_of_le_one_left hRpos.le hρ1.le
  exact hstep x hx R ((le_max_right _ _).trans hR)
    (hsmall x hx R ((le_max_left _ _).trans (hR.trans hρR)))

/-- **I5–I7.** Tilt improvement gives one unoriented direction `e₀` along which the ball tilt
decays like `r ^ (m - 2)` uniformly at all free-boundary centers, together with the uniform
kinetic mass lower bound (MC5). -/
theorem RigidityHypotheses.exists_common_tilt_direction_of_tiltImprovement
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (himp : HasBallTiltImprovement (zeroExtension g u) (frontier (epigraph g))) :
    ∃ e₀ : Space (m + 1), ‖e₀‖ = 1 ∧ ∃ c_kin D R₂ : ℝ, 0 < c_kin ∧ 1 ≤ R₂ ∧
      ∀ x ∈ frontier (epigraph g), ∀ r, R₂ ≤ r →
        c_kin * r ^ m ≤ (∫ y in closedBall x r, ‖gradient (zeroExtension g u) y‖ ^ 2) ∧
          ballTiltIntegral (zeroExtension g u) x e₀ r ≤ D * (r ^ m / r ^ 2) := by
  obtain ⟨B, R₀, hB, hR₀, hdecay⟩ :=
    hr.exists_uniform_tilt_decay_of_tiltImprovement h hsharp himp
  obtain ⟨c_kin, C_kin, R_k, hc, hC, -, hkin⟩ := hr.exists_uniform_kinetic_mass_bounds h hsharp
  have hR₂ : 1 ≤ max R₀ R_k := le_max_of_le_left hR₀
  obtain ⟨e₀, he₀, hcommon⟩ := exists_common_limiting_lineProjection
    h.zeroExtension_locallyLipschitz (frontier (epigraph g)) (R₀ := max R₀ R_k)
    (by linarith) hc hC hB
    (fun x hx r hr' ↦ hkin x hx r ((le_max_right _ _).trans hr'))
    (fun x hx r hr' ↦ hdecay x hx r ((le_max_left _ _).trans hr'))
  exact ⟨e₀, he₀, c_kin, limitingTiltConst m c_kin C_kin B, max R₀ R_k, hc, hR₂,
    fun x hx r hr' ↦ ⟨(hkin x hx r ((le_max_right _ _).trans hr')).1, (hcommon x hx).1 r hr'⟩⟩

/-! ## DS1. Normals of free-boundary blow-down limits, orientation, and the coarse cone -/

/-- **I4 at moving centers.** If the ball tilt along `e₀` decays like `r ^ (m - 2)` and the
kinetic mass is uniformly of surface order at free-boundary centers, then every halfspace
blow-down limit at free-boundary centers has inner normal `e₀` or `-e₀`. -/
theorem RigidityHypotheses.halfspace_normal_eq_or_neg_of_uniform_tilt
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {e₀ : Space (m + 1)} (he₀ : ‖e₀‖ = 1) {c_kin D R₂ : ℝ} (hc : 0 < c_kin)
    (hbounds : ∀ x ∈ frontier (epigraph g), ∀ r, R₂ ≤ r →
      c_kin * r ^ m ≤ (∫ y in closedBall x r, ‖gradient (zeroExtension g u) y‖ ^ 2) ∧
        ballTiltIntegral (zeroExtension g u) x e₀ r ≤ D * (r ^ m / r ^ 2))
    (p : ℕ → Space (m + 1)) (hp : ∀ j, p j ∈ frontier (epigraph g))
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (p j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    e = e₀ ∨ e = -e₀ := by
  have hv : LocallyLipschitz (zeroExtension g u) := h.zeroExtension_locallyLipschitz
  set A : ℝ := ‖lineProjection e₀ - lineProjection e‖ ^ 2 with hA_def
  have hA : 0 ≤ A := sq_nonneg _
  have ht := (hr.translated_energy_and_tilt_tendsto_of_halfspace_limit h hsharp p hR he hlocal
    one_pos).2.2
  have ht' : Tendsto (fun j ↦ R j ^ (-(m : ℤ)) *
      ballTiltIntegral (zeroExtension g u) (p j) e (R j)) atTop (𝓝 0) :=
    ht.congr fun j ↦ (normalized_ballTiltIntegral_eq_diffuse _ (p j) e (hR j)).symm
  have hD : Tendsto (fun j ↦ D / R j ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hRt)
  have hbound : ∀ᶠ j in atTop, A * c_kin ≤ 2 * (D / R j ^ 2) +
      2 * (R j ^ (-(m : ℤ)) * ballTiltIntegral (zeroExtension g u) (p j) e (R j)) := by
    filter_upwards [hRt.eventually_ge_atTop R₂] with j hj
    obtain ⟨hkin, htilt⟩ := hbounds (p j) (hp j) (R j) hj
    have hcomp := norm_lineProjection_sub_sq_mul_kinetic_le hv he₀ he (p j) (R j)
    have hRm : 0 < R j ^ m := pow_pos (hR j) m
    have hR2 : 0 < R j ^ 2 := pow_pos (hR j) 2
    have h1 : A * (c_kin * R j ^ m) ≤ 2 * (D * (R j ^ m / R j ^ 2)) +
        2 * ballTiltIntegral (zeroExtension g u) (p j) e (R j) := by
      calc A * (c_kin * R j ^ m)
          ≤ A * ∫ y in closedBall (p j) (R j), ‖gradient (zeroExtension g u) y‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hkin hA
        _ ≤ 2 * ballTiltIntegral (zeroExtension g u) (p j) e₀ (R j) +
            2 * ballTiltIntegral (zeroExtension g u) (p j) e (R j) := hcomp
        _ ≤ 2 * (D * (R j ^ m / R j ^ 2)) +
            2 * ballTiltIntegral (zeroExtension g u) (p j) e (R j) := by linarith
    have hzpow : R j ^ (-(m : ℤ)) = (R j ^ m)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hzpow]
    have h2 : A * c_kin = (A * (c_kin * R j ^ m)) * (R j ^ m)⁻¹ := by
      field_simp
    have h3 : (2 * (D * (R j ^ m / R j ^ 2)) +
        2 * ballTiltIntegral (zeroExtension g u) (p j) e (R j)) * (R j ^ m)⁻¹ =
        2 * (D / R j ^ 2) +
          2 * ((R j ^ m)⁻¹ * ballTiltIntegral (zeroExtension g u) (p j) e (R j)) := by
      field_simp
    rw [h2, ← h3]
    exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hRm.le)
  have hlim : Tendsto (fun j ↦ 2 * (D / R j ^ 2) +
      2 * (R j ^ (-(m : ℤ)) * ballTiltIntegral (zeroExtension g u) (p j) e (R j)))
      atTop (𝓝 0) := by
    have hsum := (hD.const_mul 2).add (ht'.const_mul 2)
    rwa [mul_zero, add_zero] at hsum
  have hA0 : A * c_kin ≤ 0 := ge_of_tendsto hlim hbound
  have hAz : A = 0 := le_antisymm (by nlinarith) hA
  have hnorm : ‖lineProjection e₀ - lineProjection e‖ = 0 := by
    rw [hA_def] at hAz
    exact (pow_eq_zero_iff two_ne_zero).mp hAz
  exact (lineProjection_eq_iff_of_unit he₀ he).mp (sub_eq_zero.mp (norm_eq_zero.mp hnorm))

/-- Along a halfspace blow-down limit with inner normal `e`, the antipodal difference
`v (p + R • e) - v (p - R • e)` tends to one. -/
theorem RigidityHypotheses.tendsto_antipodal_sub_of_halfspace_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (p : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (p j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ zeroExtension g u (p j + R j • e) - zeroExtension g u (p j - R j • e))
      atTop (𝓝 1) := by
  have hee : 0 < inner ℝ e e := by
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
  have h1 : Tendsto (fun j ↦ zeroExtension g u (p j + R j • e)) atTop (𝓝 1) :=
    (hr.translated_tendstoUniformlyOn_one_positive_halfspace h hsharp p hR hRt he hlocal
      (isCompact_singleton (x := e))
      (fun x hx ↦ by rw [mem_singleton_iff.mp hx]; exact hee)).tendsto_at (mem_singleton e)
  have h2 : ∀ᶠ j in atTop, zeroExtension g u (p j - R j • e) = 0 := by
    filter_upwards [hr.translated_eventually_eq_zero_negative_halfspace h hsharp p hR hRt he
      hlocal (isCompact_singleton (x := -e))
      (fun x hx ↦ by rw [mem_singleton_iff.mp hx, inner_neg_right]; linarith)] with j hj
    have hj' : zeroExtension g u (p j + R j • -e) = 0 := hj (mem_singleton (-e))
    rwa [smul_neg, ← sub_eq_add_neg] at hj'
  have h3 : Tendsto (fun j ↦ zeroExtension g u (p j - R j • e)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (h2.mono fun j hj ↦ hj.symm)
  have h4 := h1.sub h3
  rwa [sub_zero] at h4

/-- For all large radii, the antipodal difference along `e₀` stays at least `1 / 2` in absolute
value at every free-boundary point (compactness, DS1). -/
theorem RigidityHypotheses.exists_antipodal_sign_radius
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {e₀ : Space (m + 1)} (he₀ : ‖e₀‖ = 1) {c_kin D R₂ : ℝ} (hc : 0 < c_kin)
    (hbounds : ∀ x ∈ frontier (epigraph g), ∀ r, R₂ ≤ r →
      c_kin * r ^ m ≤ (∫ y in closedBall x r, ‖gradient (zeroExtension g u) y‖ ^ 2) ∧
        ballTiltIntegral (zeroExtension g u) x e₀ r ≤ D * (r ^ m / r ^ 2)) :
    ∃ R_s : ℝ, 1 ≤ R_s ∧ ∀ x ∈ frontier (epigraph g), ∀ r, R_s ≤ r →
      1 / 2 ≤ |zeroExtension g u (x + r • e₀) - zeroExtension g u (x - r • e₀)| := by
  by_contra hcon
  push Not at hcon
  have hseq (n : ℕ) : ∃ x ∈ frontier (epigraph g), ∃ r : ℝ, (n : ℝ) + 1 ≤ r ∧
      |zeroExtension g u (x + r • e₀) - zeroExtension g u (x - r • e₀)| < 1 / 2 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact hcon ((n : ℝ) + 1) (by linarith)
  choose p hp R hRn hsmall using hseq
  obtain ⟨hR1, hRt⟩ := one_le_and_tendsto_of_succ_le hRn
  obtain ⟨φ, hφ, e, he, hlocal⟩ := hr.exists_frontier_halfspace_subseq h hsharp p hp hR1 hRt
  have hRpos : ∀ j, 0 < R (φ j) := fun j ↦ zero_lt_one.trans_le (hR1 (φ j))
  have hRt' : Tendsto (fun j ↦ R (φ j)) atTop atTop := hRt.comp hφ.tendsto_atTop
  have hlim := hr.tendsto_antipodal_sub_of_halfspace_limit h hsharp (fun j ↦ p (φ j)) hRpos
    hRt' he hlocal
  obtain ⟨j, hj⟩ := (hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))).exists
  have hs := abs_lt.mp (hsmall (φ j))
  rcases hr.halfspace_normal_eq_or_neg_of_uniform_tilt h hsharp he₀ hc hbounds
      (fun j ↦ p (φ j)) (fun j ↦ hp (φ j)) hRpos hRt' he hlocal with he' | he'
  · have hj' : 1 / 2 < zeroExtension g u (p (φ j) + R (φ j) • e₀) -
        zeroExtension g u (p (φ j) - R (φ j) • e₀) := by
      rw [he'] at hj
      exact hj
    linarith [hs.2]
  · have hj' : 1 / 2 < zeroExtension g u (p (φ j) - R (φ j) • e₀) -
        zeroExtension g u (p (φ j) + R (φ j) • e₀) := by
      rw [he'] at hj
      have hpt1 : p (φ j) + R (φ j) • -e₀ = p (φ j) - R (φ j) • e₀ := by
        rw [smul_neg, ← sub_eq_add_neg]
      have hpt2 : p (φ j) - R (φ j) • -e₀ = p (φ j) + R (φ j) • e₀ := by
        rw [smul_neg, sub_neg_eq_add]
      have hj2 : 1 / 2 < zeroExtension g u (p (φ j) + R (φ j) • -e₀) -
          zeroExtension g u (p (φ j) - R (φ j) • -e₀) := hj
      rwa [hpt1, hpt2] at hj2
    linarith [hs.1]

/-- **DS1 orientation.** The antipodal sign is constant on the connected set of pairs
(boundary point, large radius), which selects one orientation `eo = ±e₀`. -/
theorem Hypotheses.exists_oriented_antipodal_direction (h : Hypotheses g u f κ)
    {e₀ : Space (m + 1)} {R_s : ℝ}
    (hsign : ∀ x ∈ frontier (epigraph g), ∀ r, R_s ≤ r →
      1 / 2 ≤ |zeroExtension g u (x + r • e₀) - zeroExtension g u (x - r • e₀)|) :
    ∃ eo : Space (m + 1), (eo = e₀ ∨ eo = -e₀) ∧ ∀ x ∈ frontier (epigraph g), ∀ r, R_s ≤ r →
      1 / 2 ≤ zeroExtension g u (x + r • eo) - zeroExtension g u (x - r • eo) := by
  have hg : Continuous g := h.graph_contDiff.continuous
  have hv : Continuous (zeroExtension g u) := h.zeroExtension_locallyLipschitz.continuous
  have hpt : Continuous (fun q : Space m × ℝ ↦ point q.1 (g q.1)) :=
    pointContinuousLinearMap.continuous.comp (continuous_fst.prodMk (hg.comp continuous_fst))
  let F : Space m × ℝ → ℝ := fun q ↦ zeroExtension g u (point q.1 (g q.1) + q.2 • e₀) -
    zeroExtension g u (point q.1 (g q.1) - q.2 • e₀)
  have hF : Continuous F :=
    (hv.comp (hpt.add (continuous_snd.smul continuous_const))).sub
      (hv.comp (hpt.sub (continuous_snd.smul continuous_const)))
  have hT : IsPreconnected ((univ : Set (Space m)) ×ˢ Ici R_s) :=
    isPreconnected_univ.prod isPreconnected_Ici
  have habs : ∀ q ∈ (univ : Set (Space m)) ×ˢ Ici R_s, 1 / 2 ≤ |F q| :=
    fun q hq ↦ hsign _ (point_mem_frontier_epigraph hg q.1) q.2 hq.2
  have hrepr : ∀ x ∈ frontier (epigraph g), point (horizontal x) (g (horizontal x)) = x := by
    intro x hx
    rw [frontier_epigraph hg] at hx
    have hx' : g (horizontal x) = x (Fin.last m) := hx
    rw [hx', point_horizontal_last]
  rcases forall_le_or_forall_le_neg_of_le_abs hT hF.continuousOn (by norm_num) habs with
    hpos | hneg
  · refine ⟨e₀, Or.inl rfl, fun x hx r hr' ↦ ?_⟩
    have hq : 1 / 2 ≤ F (horizontal x, r) := hpos (horizontal x, r) ⟨mem_univ _, hr'⟩
    simp only [F, hrepr x hx] at hq
    exact hq
  · refine ⟨-e₀, Or.inr rfl, fun x hx r hr' ↦ ?_⟩
    have hq : F (horizontal x, r) ≤ -(1 / 2) := hneg (horizontal x, r) ⟨mem_univ _, hr'⟩
    simp only [F, hrepr x hx] at hq
    rw [smul_neg, sub_neg_eq_add, ← sub_eq_add_neg]
    linarith

/-- With the orientation fixed by the antipodal sign, every halfspace blow-down limit at
free-boundary centers has inner normal exactly `eo`. -/
theorem RigidityHypotheses.halfspace_normal_eq_of_oriented
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {e₀ : Space (m + 1)} (he₀ : ‖e₀‖ = 1) {c_kin D R₂ : ℝ} (hc : 0 < c_kin)
    (hbounds : ∀ x ∈ frontier (epigraph g), ∀ r, R₂ ≤ r →
      c_kin * r ^ m ≤ (∫ y in closedBall x r, ‖gradient (zeroExtension g u) y‖ ^ 2) ∧
        ballTiltIntegral (zeroExtension g u) x e₀ r ≤ D * (r ^ m / r ^ 2))
    {eo : Space (m + 1)} (heo : eo = e₀ ∨ eo = -e₀) {R_s : ℝ}
    (horient : ∀ x ∈ frontier (epigraph g), ∀ r, R_s ≤ r →
      1 / 2 ≤ zeroExtension g u (x + r • eo) - zeroExtension g u (x - r • eo))
    (p : ℕ → Space (m + 1)) (hp : ∀ j, p j ∈ frontier (epigraph g))
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (p j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    e = eo := by
  have h1 := hr.halfspace_normal_eq_or_neg_of_uniform_tilt h hsharp he₀ hc hbounds p hp hR hRt
    he hlocal
  have h2 : e = eo ∨ e = -eo := by
    rcases heo with heo | heo <;> rcases h1 with h1 | h1
    · left
      rw [h1, heo]
    · right
      rw [h1, heo]
    · right
      rw [h1, heo, neg_neg]
    · left
      rw [h1, heo]
  rcases h2 with h2 | h2
  · exact h2
  · exfalso
    have hlim := hr.tendsto_antipodal_sub_of_halfspace_limit h hsharp p hR hRt he hlocal
    rw [h2] at hlim
    have hev : ∀ᶠ j in atTop, zeroExtension g u (p j + R j • -eo) -
        zeroExtension g u (p j - R j • -eo) ≤ -(1 / 2) := by
      filter_upwards [hRt.eventually_ge_atTop R_s] with j hj
      have hh := horient (p j) (hp j) (R j) hj
      rw [smul_neg, sub_neg_eq_add, ← sub_eq_add_neg]
      linarith
    have hle := le_of_tendsto hlim hev
    linarith

/-- **DS1.1.** If every free-boundary blow-down sequence subconverges to the halfspace with inner
normal `e`, the positive phase contains a uniform coarse cone around `e` at every boundary
point. -/
theorem RigidityHypotheses.exists_positive_coarse_cone_radius
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hlim : HasFrontierHalfspaceLimits g u e)
    {η : ℝ} (hη : 0 < η) :
    ∃ R_a : ℝ, 0 < R_a ∧ ∀ p ∈ frontier (epigraph g), ∀ w : Space (m + 1), R_a ≤ ‖w‖ →
      η * ‖w‖ ≤ inner ℝ e w → p + w ∈ epigraph g := by
  by_contra hcon
  push Not at hcon
  have hseq (n : ℕ) : ∃ p ∈ frontier (epigraph g), ∃ w : Space (m + 1), (n : ℝ) + 1 ≤ ‖w‖ ∧
      η * ‖w‖ ≤ inner ℝ e w ∧ p + w ∉ epigraph g := hcon _ (by positivity)
  choose p hp w hwn hwe hwout using hseq
  obtain ⟨hR1, hRt⟩ := one_le_and_tendsto_of_succ_le (R := fun n ↦ ‖w n‖) hwn
  have hwpos : ∀ n, 0 < ‖w n‖ := fun n ↦ zero_lt_one.trans_le (hR1 n)
  let wn : ℕ → Space (m + 1) := fun n ↦ ‖w n‖⁻¹ • w n
  have hwn_norm : ∀ n, ‖wn n‖ = 1 := fun n ↦ by
    simp only [wn, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hwpos n).ne'
  have hwn_smul : ∀ n, ‖w n‖ • wn n = w n := fun n ↦ by
    simp only [wn, smul_smul, mul_inv_cancel₀ (hwpos n).ne', one_smul]
  have hwn_e : ∀ n, η ≤ inner ℝ e (wn n) := fun n ↦ by
    simp only [wn, real_inner_smul_right]
    rw [le_inv_mul_iff₀ (hwpos n)]
    linarith [hwe n, mul_comm η ‖w n‖]
  obtain ⟨wlim, -, ψ, hψ, hψlim⟩ := (isCompact_sphere (0 : Space (m + 1)) 1).tendsto_subseq
    (x := wn) (fun n ↦ by rw [mem_sphere_zero_iff_norm]; exact hwn_norm n)
  have hwlim_e : η ≤ inner ℝ e wlim :=
    ge_of_tendsto ((tendsto_const_nhds (x := e)).inner hψlim)
      (Eventually.of_forall fun n ↦ hwn_e (ψ n))
  obtain ⟨φ, hφ, hlocal⟩ := hlim (fun n ↦ p (ψ n)) (fun n ↦ hp (ψ n)) (fun n ↦ ‖w (ψ n)‖)
    (fun n ↦ hR1 (ψ n)) (hRt.comp hψ.tendsto_atTop)
  have hKpos : ∀ x ∈ closedBall wlim (η / 2), 0 < inner ℝ e x := by
    intro x hx
    have hdist : ‖x - wlim‖ ≤ η / 2 := by rwa [mem_closedBall, dist_eq_norm] at hx
    have hcs : |inner ℝ e (x - wlim)| ≤ ‖x - wlim‖ := by
      have hh := abs_real_inner_le_norm e (x - wlim)
      rwa [he, one_mul] at hh
    have hsplit : inner ℝ e x = inner ℝ e wlim + inner ℝ e (x - wlim) := by
      rw [inner_sub_right]
      ring
    rw [hsplit]
    linarith [neg_abs_le (inner ℝ e (x - wlim))]
  have hunif := hr.translated_tendstoUniformlyOn_one_positive_halfspace h hsharp
    (fun n ↦ p (ψ (φ n))) (fun n ↦ hwpos (ψ (φ n)))
    ((hRt.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop) he hlocal
    (isCompact_closedBall wlim (η / 2)) hKpos
  have hev1 := Metric.tendstoUniformlyOn_iff.mp hunif (1 / 2) (by norm_num)
  have hev2 : ∀ᶠ n in atTop, wn (ψ (φ n)) ∈ closedBall wlim (η / 2) :=
    (hψlim.comp hφ.tendsto_atTop).eventually_mem (closedBall_mem_nhds wlim (by positivity))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hval : dist (1 : ℝ) (zeroExtension g u (p (ψ (φ n)) + ‖w (ψ (φ n))‖ • wn (ψ (φ n)))) <
      1 / 2 := hn1 _ hn2
  rw [hwn_smul, Real.dist_eq] at hval
  have hpos : 0 < zeroExtension g u (p (ψ (φ n)) + w (ψ (φ n))) := by
    have hh := (abs_lt.mp hval).2
    linarith
  exact hwout (ψ (φ n)) ((h.zeroExtension_pos_iff _).mp hpos)

/-- **DS1.2.** If every free-boundary blow-down sequence subconverges to the halfspace with inner
normal `e`, the zero phase contains a uniform coarse cone around `-e` at every boundary point. -/
theorem RigidityHypotheses.exists_negative_coarse_cone_radius
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hlim : HasFrontierHalfspaceLimits g u e)
    {η : ℝ} (hη : 0 < η) :
    ∃ R_b : ℝ, 0 < R_b ∧ ∀ p ∈ frontier (epigraph g), ∀ w : Space (m + 1), R_b ≤ ‖w‖ →
      inner ℝ e w ≤ -η * ‖w‖ → p + w ∉ epigraph g := by
  by_contra hcon
  push Not at hcon
  have hseq (n : ℕ) : ∃ p ∈ frontier (epigraph g), ∃ w : Space (m + 1), (n : ℝ) + 1 ≤ ‖w‖ ∧
      inner ℝ e w ≤ -η * ‖w‖ ∧ p + w ∈ epigraph g := hcon _ (by positivity)
  choose p hp w hwn hwe hwin using hseq
  obtain ⟨hR1, hRt⟩ := one_le_and_tendsto_of_succ_le (R := fun n ↦ ‖w n‖) hwn
  have hwpos : ∀ n, 0 < ‖w n‖ := fun n ↦ zero_lt_one.trans_le (hR1 n)
  let wn : ℕ → Space (m + 1) := fun n ↦ ‖w n‖⁻¹ • w n
  have hwn_norm : ∀ n, ‖wn n‖ = 1 := fun n ↦ by
    simp only [wn, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hwpos n).ne'
  have hwn_smul : ∀ n, ‖w n‖ • wn n = w n := fun n ↦ by
    simp only [wn, smul_smul, mul_inv_cancel₀ (hwpos n).ne', one_smul]
  have hwn_e : ∀ n, inner ℝ e (wn n) ≤ -η := fun n ↦ by
    simp only [wn, real_inner_smul_right]
    rw [inv_mul_le_iff₀ (hwpos n)]
    linarith [hwe n, mul_comm (-η) ‖w n‖]
  obtain ⟨wlim, -, ψ, hψ, hψlim⟩ := (isCompact_sphere (0 : Space (m + 1)) 1).tendsto_subseq
    (x := wn) (fun n ↦ by rw [mem_sphere_zero_iff_norm]; exact hwn_norm n)
  have hwlim_e : inner ℝ e wlim ≤ -η :=
    le_of_tendsto ((tendsto_const_nhds (x := e)).inner hψlim)
      (Eventually.of_forall fun n ↦ hwn_e (ψ n))
  obtain ⟨φ, hφ, hlocal⟩ := hlim (fun n ↦ p (ψ n)) (fun n ↦ hp (ψ n)) (fun n ↦ ‖w (ψ n)‖)
    (fun n ↦ hR1 (ψ n)) (hRt.comp hψ.tendsto_atTop)
  have hKneg : ∀ x ∈ closedBall wlim (η / 2), inner ℝ e x < 0 := by
    intro x hx
    have hdist : ‖x - wlim‖ ≤ η / 2 := by rwa [mem_closedBall, dist_eq_norm] at hx
    have hcs : |inner ℝ e (x - wlim)| ≤ ‖x - wlim‖ := by
      have hh := abs_real_inner_le_norm e (x - wlim)
      rwa [he, one_mul] at hh
    have hsplit : inner ℝ e x = inner ℝ e wlim + inner ℝ e (x - wlim) := by
      rw [inner_sub_right]
      ring
    rw [hsplit]
    linarith [le_abs_self (inner ℝ e (x - wlim))]
  have hev1 := hr.translated_eventually_eq_zero_negative_halfspace h hsharp
    (fun n ↦ p (ψ (φ n))) (fun n ↦ hwpos (ψ (φ n)))
    ((hRt.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop) he hlocal
    (isCompact_closedBall wlim (η / 2)) hKneg
  have hev2 : ∀ᶠ n in atTop, wn (ψ (φ n)) ∈ closedBall wlim (η / 2) :=
    (hψlim.comp hφ.tendsto_atTop).eventually_mem (closedBall_mem_nhds wlim (by positivity))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hval : zeroExtension g u (p (ψ (φ n)) + ‖w (ψ (φ n))‖ • wn (ψ (φ n))) = 0 := hn1 hn2
  rw [hwn_smul] at hval
  have hpos := (h.zeroExtension_pos_iff _).mpr (hwin (ψ (φ n)))
  rw [hval] at hpos
  exact lt_irrefl _ hpos

/-- **DS1.** Halfspace blow-down limits with a common inner normal `e` at all free-boundary
centers give a uniform boundary coarse cone along `e`. -/
theorem RigidityHypotheses.hasUniformBoundaryCoarseCone_of_frontierHalfspaceLimits
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hlim : HasFrontierHalfspaceLimits g u e) :
    HasUniformBoundaryCoarseCone g e := by
  intro η hη
  obtain ⟨Ra, hRa, hA⟩ := hr.exists_positive_coarse_cone_radius h hsharp he hlim hη.1
  obtain ⟨Rb, -, hB⟩ := hr.exists_negative_coarse_cone_radius h hsharp he hlim hη.1
  refine ⟨max Ra Rb, lt_max_of_lt_left hRa, fun p hp w hw ↦ ⟨fun hpos ↦ ?_, fun hneg ↦ ?_⟩⟩
  · exact hA p hp w ((le_max_left _ _).trans hw) hpos
  · exact hB p hp w ((le_max_right _ _).trans hw) hneg

/-! ## Main theorem -/

/-- **Flatness transfer modulo the local tilt improvement.** One halfspace blow-down limit of the
zero extension, together with the uniform stopped tilt improvement at free-boundary centers
(blueprint HA12), yields a uniform boundary coarse cone. The halfspace
`{y | 0 < inner ℝ e y}` is `positiveHalfspace e`. -/
theorem RigidityHypotheses.exists_uniformBoundaryCoarseCone_of_halfspace_limit_of_tiltImprovement
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (himp : HasBallTiltImprovement (zeroExtension g u) (frontier (epigraph g))) :
    ∃ e' : Space (m + 1), ‖e'‖ = 1 ∧ HasUniformBoundaryCoarseCone g e' := by
  have hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m :=
    fun z ρ hρ ↦ hr.phaseEnergy_le_planar_mass_of_halfspace_limit h hR hRt he hlocal z hρ
  obtain ⟨e₀, he₀, c_kin, D, R₂, hc, -, hbounds⟩ :=
    hr.exists_common_tilt_direction_of_tiltImprovement h hsharp himp
  obtain ⟨R_s, -, hsign⟩ := hr.exists_antipodal_sign_radius h hsharp he₀ hc hbounds
  obtain ⟨eo, heo, horient⟩ := h.exists_oriented_antipodal_direction hsign
  have heo_norm : ‖eo‖ = 1 := by
    rcases heo with heo | heo
    · rw [heo, he₀]
    · rw [heo, norm_neg, he₀]
  refine ⟨eo, heo_norm, hr.hasUniformBoundaryCoarseCone_of_frontierHalfspaceLimits h hsharp
    heo_norm ?_⟩
  intro c hc' R' hR' hRt'
  obtain ⟨φ, hφ, e', he', hloc'⟩ := hr.exists_frontier_halfspace_subseq h hsharp c hc' hR' hRt'
  have heq : e' = eo := hr.halfspace_normal_eq_of_oriented h hsharp he₀ hc hbounds heo horient
    (fun j ↦ c (φ j)) (fun j ↦ hc' (φ j)) (fun j ↦ zero_lt_one.trans_le (hR' (φ j)))
    (hRt'.comp hφ.tendsto_atTop) he' hloc'
  subst heq
  exact ⟨φ, hφ, hloc'⟩

end SerrinEpigraph
