module

public import SerrinEpigraph.UniformKineticMass
public import SerrinEpigraph.PlaneTiltTranslatedClearing

/-!
# Mesoscopic flatness of interior level sets (HA9.c, HA9.d)

Blueprint `harmonic-approximation.md`, HA9.c (mesoscopic zero-parameter limits) and the
mesoscopic part of HA9.d (no repeated layers, without a specified modulus).

* `RigidityHypotheses.translated_not_constant_phase_limit_of_level`: diverging dilations centered
  at points of a fixed interior value range cannot converge to a constant phase.
* `RigidityHypotheses.exists_level_halfspace_subseq` (HA9.c): such dilations have a subsequence
  converging locally in `L¹` to a halfspace whose boundary plane passes through the origin
  (SD2 for the limiting phase, as in `RigidityHypotheses.exists_frontier_halfspace_subseq`).
* `RigidityHypotheses.exists_mesoscopic_flatness` (HA9.d, mesoscopic): for `η > 0` there are
  `M, ℓ > 0` such that, at every interior level point `X` whose tilt along a unit vector `e` on
  `B̄_d(X)` is below `ℓ dᵐ` with `d ≥ M`, every interior level point of `B̄_d(X)` lies within
  `η d` of the hyperplane through `X` orthogonal to `e`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ### HA9.c: halfspace limits at interior level centers -/

/-- Diverging dilations centered at points with values in a fixed compact subinterval of
`(0, 1)` cannot converge locally in `L¹` to a constant phase. -/
theorem RigidityHypotheses.translated_not_constant_phase_limit_of_level
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) (c : ℕ → Space (m + 1))
    (hc : ∀ j, zeroExtension g u (c j) ∈ Icc a b)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {a₀ : ℝ} (ha₀ : a₀ = 0 ∨ a₀ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c j + R j • x) - a₀‖)
        atTop (𝓝 0)) : False := by
  let U : ℕ → Space (m + 1) → ℝ := fun j x ↦ zeroExtension g u (c j + R j • x)
  have hRp : ∀ j, 0 < R j := fun j ↦ zero_lt_one.trans_le (hR j)
  have hU (j : ℕ) : LocallyLipschitz (U j) :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz (c j) (R j)
  have hUv (j : ℕ) (x : Space (m + 1)) : U j x ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hav : a₀ ∈ Icc (0 : ℝ) 1 := by rcases ha₀ with rfl | rfl <;> norm_num
  have hEc (j : ℕ) (x : Space (m + 1)) :
      rescaledPhaseEnergyDensity f (R j) (fun _ : Space (m + 1) ↦ a₀) x = 0 := by
    exact rescaledPhaseEnergyDensity_eq_zero_of_endpoint f (R j) (fun _ ↦ hav) ha₀
  let A : Set (Space (m + 1)) := closedBall 0 (1 + 1 : ℝ) \ ball 0 1
  have hA : IsCompact A := (isCompact_closedBall 0 _).diff isOpen_ball
  have hEB (j : ℕ) :
      (∫ x in A, rescaledPhaseEnergyDensity f (R j) (U j) x) +
      (∫ x in A, rescaledPhaseEnergyDensity f (R j) (fun _ ↦ a₀) x) ≤ L * (1 + 1) ^ m := by
    simp only [hEc, integral_zero, add_zero]
    apply (setIntegral_mono_set
      (h.integrableOn_rescaledPhaseEnergy (hU j) (hUv j) (R j) (isCompact_closedBall 0 _))
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRp j).le (hUv j)))
      (Eventually.of_forall sdiff_subset)).trans
    exact hr.translated_rescaled_energy_le_surface_bound h hbound (c j) (hRp j)
      (by norm_num)
  obtain ⟨η, ε, hε, hglue⟩ := hr.exists_annular_gluing_sequence h hU
    (fun _ ↦ (LipschitzWith.const a₀).locallyLipschitz) hUv (fun _ _ ↦ hav)
    (r := 1) (t := 1) (by norm_num) (by norm_num)
    (continuousOn_const.integrableOn_compact hA) hR hRt hEB (hlocal A hA)
    (by simpa only [sub_self, norm_zero, integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)))
  have hupper (j : ℕ) :
      (∫ x in ball 0 1, rescaledPhaseEnergyDensity f (R j) (U j) x) ≤ ε j := by
    obtain ⟨hη, _, hs, hone, hηv, hcomp⟩ := hglue j
    have hh := hr.translated_inner_energy_le_of_glued_comparison h (c j) (hRp j)
      (by norm_num : (0 : ℝ) ≤ 1) (LipschitzWith.const a₀).locallyLipschitz hη.locallyLipschitz
      (fun _ ↦ hav) hηv (hs.trans ball_subset_closedBall) hone hcomp
    simpa only [hEc, integral_zero, zero_add] using hh
  obtain ⟨ρ, C, _, hC, hlo⟩ := hr.exists_translated_level_energy_lower_bound h ha hb
  have hlarge : ∀ᶠ j in atTop, ρ ≤ R j * (1 / 2 : ℝ) := by
    filter_upwards [hRt.eventually (eventually_ge_atTop (2 * ρ))] with j hj
    linarith
  have hpositive : 0 < C * (1 / 2 : ℝ) ^ m := mul_pos hC (pow_pos (by norm_num) _)
  have hevent := hε.eventually (gt_mem_nhds hpositive)
  obtain ⟨j, hj, hjlarge⟩ := (hevent.and hlarge).exists
  have hdensity := hlo (c j) (R j) (hRp j) 0 (by simpa using hc j) (1 / 2) hjlarge
  have hmono : (∫ x in closedBall 0 (1 / 2 : ℝ),
      rescaledPhaseEnergyDensity f (R j) (U j) x) ≤
      ∫ x in ball 0 1, rescaledPhaseEnergyDensity f (R j) (U j) x := by
    apply setIntegral_mono_set
      ((h.integrableOn_rescaledPhaseEnergy (hU j) (hUv j) (R j)
        (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall)
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRp j).le (hUv j)))
    exact Eventually.of_forall (closedBall_subset_ball (by norm_num))
  exact (not_lt_of_ge ((hdensity.trans hmono).trans (hupper j))) hj

/-- **HA9.c at interior level centers.** Under the sharp all-center planar energy bound, every
family of diverging dilations centered at points with values in a fixed compact subinterval of
`(0, 1)` has a subsequence converging locally in `L¹` to a halfspace whose boundary plane passes
through the origin. -/
theorem RigidityHypotheses.exists_level_halfspace_subseq
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) (c : ℕ → Space (m + 1))
    (hc : ∀ j, zeroExtension g u (c j) ∈ Icc a b)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ e : Space (m + 1), ‖e‖ = 1 ∧
      ∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c (φ j) + R (φ j) • x) -
          {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0) := by
  obtain ⟨φ, hφ, E, hEm, hlim⟩ := hr.translated_measurable_phase_limit h hsharp c
    (fun j ↦ zero_lt_one.trans_le (hR j)) hRt
  let c' : ℕ → Space (m + 1) := fun j ↦ c (φ j)
  let R' : ℕ → ℝ := fun j ↦ R (φ j)
  have hR' : ∀ j, 1 ≤ R' j := fun j ↦ hR (φ j)
  have hR'pos : ∀ j, 0 < R' j := fun j ↦ zero_lt_one.trans_le (hR' j)
  have hRt' : Tendsto R' atTop atTop := hRt.comp hφ.tendsto_atTop
  have hlimE : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c' j + R' j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := fun K hK ↦ (hlim K hK).2
  -- nontriviality of the limiting phase
  have hnot {a₀ : ℝ} (ha₀ : a₀ = 0 ∨ a₀ = 1)
      (he : ∀ᵐ x ∂volume, E.indicator (fun _ ↦ (1 : ℝ)) x = a₀) : False := by
    apply hr.translated_not_constant_phase_limit_of_level h hsharp ha hb c' (fun j ↦ hc (φ j))
      hR' hRt' ha₀
    intro K hK
    convert hlimE K hK using 1
    funext j
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae he] with x hx
    rw [hx]
  have hE0 : volume E ≠ 0 := by
    intro hz
    apply hnot (a₀ := 0) (Or.inl rfl)
    have he : ∀ᵐ x ∂volume, x ∉ E := by simpa only [ae_iff, not_not, ofPred_mem_eq] using hz
    filter_upwards [he] with x hx
    exact indicator_of_notMem hx _
  have hEc0 : volume Eᶜ ≠ 0 := by
    intro hz
    apply hnot (a₀ := 1) (Or.inr rfl)
    have he : ∀ᵐ x ∂volume, x ∈ E := mem_ae_iff.mpr hz
    filter_upwards [he] with x hx
    exact indicator_of_mem hx _
  -- SD2 for the limiting phase
  let bas := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hPbound (z : Space (m + 1)) (r : ℝ) (hr0 : 0 < r) :
      variationalPerimeter bas E (ball z r) ≤
        ENNReal.ofReal (volume.real (closedBall (0 : Space m) 1) * r ^ m) :=
    hr.translated_limiting_phase_sharp_perimeter_bound h hsharp c' hR'pos hEm hlimE bas z r hr0
  have hPE (n : ℕ) : variationalPerimeter bas E (ball 0 ((n : ℝ) + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hPbound 0 _ (by positivity))
  have hmin : IsLocalPerimeterMinimizer bas E univ :=
    isLocalPerimeterMinimizer_univ bas hEm hPE fun U D K hU hD hK hKU hED ↦
      hr.translated_limiting_phase_open_minimality h hsharp bas c' hR' hRt' hEm hD hlimE
        hK hU hKU hED
  obtain ⟨x₀, e, he, hae⟩ := hmin.ae_eq_affine_halfspace_of_sharp_density hE0 hEc0 hPbound
  have hEH : E =ᵐ[volume] {x : Space (m + 1) | 0 < inner ℝ e (x - x₀)} :=
    eventuallyEqSet_iff.mpr hae
  have hlimH := tendsto_local_indicator_congr_ae hEH hlimE
  let c'' : ℕ → Space (m + 1) := fun j ↦ c' j + R' j • x₀
  have hUcont (j : ℕ) : Continuous (fun x ↦ zeroExtension g u (c' j + R' j • x)) :=
    (locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz
      (c' j) (R' j)).continuous
  have hshift : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c'' j + R' j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0) := by
    intro K hK
    have hs := tendsto_local_halfspace_indicator_shift
      (U := fun j x ↦ zeroExtension g u (c' j + R' j • x)) hUcont e x₀ hlimH K hK
    refine hs.congr fun j ↦ ?_
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [c'', smul_add, add_assoc]
  have hpt : ∀ j, c'' j + R' j • (-x₀) = c' j := by
    intro j
    simp only [c'', smul_neg]
    exact add_neg_cancel_right _ _
  -- the boundary plane passes through the origin
  have hplane : inner ℝ e x₀ = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hu := hr.translated_tendstoUniformlyOn_one_positive_halfspace h hsharp c'' hR'pos hRt'
        he hshift (isCompact_singleton (x := -x₀)) (by
          intro x hx
          rw [mem_singleton_iff.mp hx, inner_neg_right]
          linarith)
      have h1 := hu.tendsto_at (mem_singleton (-x₀))
      simp only [hpt] at h1
      have h2 : ∀ j, zeroExtension g u (c' j) ≤ b := fun j ↦ (hc (φ j)).2
      have h3 : (1 : ℝ) ≤ b := le_of_tendsto' h1 h2
      linarith
    · have hev := hr.translated_eventually_eq_zero_negative_halfspace h hsharp c'' hR'pos hRt'
        he hshift (isCompact_singleton (x := -x₀)) (by
          intro x hx
          rw [mem_singleton_iff.mp hx, inner_neg_right]
          linarith)
      obtain ⟨j, hj⟩ := hev.exists
      have h1 := hj (mem_singleton (-x₀))
      simp only [hpt, Pi.zero_apply] at h1
      have h2 := (hc (φ j)).1
      change a ≤ zeroExtension g u (c' j) at h2
      linarith
  refine ⟨φ, hφ, e, he, fun K hK ↦ ?_⟩
  have hset : {x : Space (m + 1) | 0 < inner ℝ e (x - x₀)} =
      {y : Space (m + 1) | 0 < inner ℝ e y} := by
    ext x
    simp only [mem_ofPred_eq, inner_sub_right, hplane, sub_zero]
  have hK' := hlimH K hK
  rw [hset] at hK'
  exact hK'

/-! ### Normals of halfspace limits under small tilt -/

/-- Squares of inner products against nearby unit vectors. -/
theorem abs_inner_sq_sub_inner_sq_le {d : ℕ} (G a b : Space d) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) :
    |inner ℝ G a ^ 2 - inner ℝ G b ^ 2| ≤ 2 * ‖G‖ ^ 2 * ‖a - b‖ := by
  have h1 : inner ℝ G a ^ 2 - inner ℝ G b ^ 2 = inner ℝ G (a - b) * inner ℝ G (a + b) := by
    rw [inner_sub_right, inner_add_right]
    ring
  rw [h1, abs_mul]
  have h2 : |inner ℝ G (a - b)| ≤ ‖G‖ * ‖a - b‖ := abs_real_inner_le_norm _ _
  have h3 : |inner ℝ G (a + b)| ≤ ‖G‖ * 2 := by
    calc |inner ℝ G (a + b)| ≤ ‖G‖ * ‖a + b‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖G‖ * 2 := mul_le_mul_of_nonneg_left
          ((norm_add_le _ _).trans (by rw [ha, hb]; norm_num)) (norm_nonneg _)
  calc |inner ℝ G (a - b)| * |inner ℝ G (a + b)| ≤ (‖G‖ * ‖a - b‖) * (‖G‖ * 2) :=
        mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
    _ = 2 * ‖G‖ ^ 2 * ‖a - b‖ := by ring

/-- The ball tilt along a nearby unit vector. -/
theorem ballTiltIntegral_le_of_unit {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v)
    {a b : Space d} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (x : Space d) (r : ℝ) :
    ballTiltIntegral v x a r ≤
      ballTiltIntegral v x b r + 2 * ‖a - b‖ * ∫ y in closedBall x r, ‖gradient v y‖ ^ 2 := by
  have hK := isCompact_closedBall x r
  have hia := integrableOn_ballTiltIntegrand hv hK a
  have hib := integrableOn_ballTiltIntegrand hv hK b
  have hg := integrableOn_gradient_sq_of_locallyLipschitz hv hK
  unfold ballTiltIntegral
  rw [← integral_const_mul, ← integral_add hib (hg.const_mul _)]
  apply setIntegral_mono_on hia (hib.add (hg.const_mul _)) measurableSet_closedBall
  intro y _
  have hpt := abs_inner_sq_sub_inner_sq_le (gradient v y) b a hb ha
  rw [norm_sub_rev] at hpt
  have := (abs_le.mp hpt).2
  simp only [Pi.add_apply]
  linarith [this]

/-- **Normals of small-tilt halfspace limits.** If dilations about moving centers converge to the
halfspace with inner normal `e`, and the normalized tilt along unit vectors `e_j → e₀` vanishes,
then `e = ± e₀`. -/
theorem RigidityHypotheses.halfspace_normal_eq_or_neg_of_small_tilt
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (ev : ℕ → Space (m + 1)) (hev : ∀ j, ‖ev j‖ = 1) {e₀ : Space (m + 1)} (he₀ : ‖e₀‖ = 1)
    (hconv : Tendsto ev atTop (𝓝 e₀))
    (htilt : Tendsto (fun j ↦ (R j ^ m)⁻¹ * ballTiltIntegral (zeroExtension g u) (c j) (ev j) (R j))
      atTop (𝓝 0)) :
    e = e₀ ∨ e = -e₀ := by
  have hv : LocallyLipschitz (zeroExtension g u) := h.zeroExtension_locallyLipschitz
  set σω : ℝ := phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) with hσω
  have hσω0 : 0 < σω := mul_pos (hr.phasePrimitive_one_pos h)
    (by
      rw [Measure.real]
      exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
        (measure_closedBall_lt_top (μ := volume)).ne)
  set A : ℝ := ‖lineProjection e₀ - lineProjection e‖ ^ 2 with hA
  have hA0 : 0 ≤ A := sq_nonneg _
  set kin : ℕ → ℝ := fun j ↦ ∫ y in closedBall (c j) (R j), ‖gradient (zeroExtension g u) y‖ ^ 2
    with hkin
  have hlim := hr.translated_energy_and_tilt_tendsto_of_halfspace_limit h hsharp c hR he hlocal
    one_pos
  -- the kinetic mass is of surface order
  have hPmass : Tendsto (fun j ↦ ∫ x in closedBall 0 1,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c j + R j • y))) x‖)
      atTop (𝓝 σω) := by
    have h1 := hlim.1
    simp only [one_pow, one_mul] at h1
    exact h1
  have hkinlow : ∀ᶠ j in atTop, σω / 4 ≤ (R j ^ m)⁻¹ * kin j := by
    filter_upwards [hPmass.eventually (lt_mem_nhds (show 3 * σω / 4 < σω by linarith))] with j hj
    have hpm := hr.primitive_mass_le_kinetic_add_half h hsharp (c j) (hR j)
    have : (3 * σω / 4) < (R j ^ m)⁻¹ * kin j + σω / 2 := hj.trans_le hpm
    linarith
  have hkinup : ∀ j, (R j ^ m)⁻¹ * kin j ≤ 2 * σω := by
    intro j
    have hk := hr.kinetic_closedBall_le_of_sharp h hsharp (c j) (hR j)
    have hRm : 0 < R j ^ m := pow_pos (hR j) m
    rw [inv_mul_le_iff₀ hRm]
    linarith [mul_comm (2 * σω) (R j ^ m)]
  have htilt' : Tendsto (fun j ↦ (R j ^ m)⁻¹ *
      ballTiltIntegral (zeroExtension g u) (c j) e (R j)) atTop (𝓝 0) := by
    refine hlim.2.2.congr fun j ↦ ?_
    rw [← normalized_ballTiltIntegral_eq_diffuse _ (c j) e (hR j), zpow_neg, zpow_natCast]
  have hdist : Tendsto (fun j ↦ ‖ev j - e₀‖) atTop (𝓝 0) := by
    have := (hconv.sub (tendsto_const_nhds (x := e₀))).norm
    simpa using this
  -- the comparison along the sequence
  have hbound : ∀ᶠ j in atTop, A * (σω / 4) ≤ 2 * ((R j ^ m)⁻¹ *
      ballTiltIntegral (zeroExtension g u) (c j) (ev j) (R j)) + 8 * σω * ‖ev j - e₀‖ +
      2 * ((R j ^ m)⁻¹ * ballTiltIntegral (zeroExtension g u) (c j) e (R j)) := by
    filter_upwards [hkinlow] with j hj
    have hRm : 0 < R j ^ m := pow_pos (hR j) m
    have hcomp := norm_lineProjection_sub_sq_mul_kinetic_le hv he₀ he (c j) (R j)
    have hnear := ballTiltIntegral_le_of_unit hv he₀ (hev j) (c j) (R j)
    have hnear' : ‖e₀ - ev j‖ = ‖ev j - e₀‖ := norm_sub_rev _ _
    rw [hnear'] at hnear
    have hscaled : A * ((R j ^ m)⁻¹ * kin j) ≤
        2 * ((R j ^ m)⁻¹ * ballTiltIntegral (zeroExtension g u) (c j) (ev j) (R j)) +
        4 * ‖ev j - e₀‖ * ((R j ^ m)⁻¹ * kin j) +
        2 * ((R j ^ m)⁻¹ * ballTiltIntegral (zeroExtension g u) (c j) e (R j)) := by
      have hinv : 0 < (R j ^ m)⁻¹ := inv_pos.mpr hRm
      have h1 : A * kin j ≤ 2 * ballTiltIntegral (zeroExtension g u) (c j) (ev j) (R j) +
          4 * ‖ev j - e₀‖ * kin j +
          2 * ballTiltIntegral (zeroExtension g u) (c j) e (R j) := by
        change A * kin j ≤ _ at hcomp
        nlinarith [hcomp, hnear]
      have h2 := mul_le_mul_of_nonneg_left h1 hinv.le
      nlinarith [h2]
    have hk1 := mul_le_mul_of_nonneg_left hj hA0
    have hk2 := mul_le_mul_of_nonneg_left (hkinup j)
      (by positivity : (0 : ℝ) ≤ 4 * ‖ev j - e₀‖)
    nlinarith [hscaled, hk1, hk2]
  have hlim0 : Tendsto (fun j ↦ 2 * ((R j ^ m)⁻¹ *
      ballTiltIntegral (zeroExtension g u) (c j) (ev j) (R j)) + 8 * σω * ‖ev j - e₀‖ +
      2 * ((R j ^ m)⁻¹ * ballTiltIntegral (zeroExtension g u) (c j) e (R j))) atTop (𝓝 0) := by
    have := ((htilt.const_mul 2).add (hdist.const_mul (8 * σω))).add (htilt'.const_mul 2)
    simpa using this
  have hA4 : A * (σω / 4) ≤ 0 := ge_of_tendsto hlim0 hbound
  have hAz : A = 0 := by
    have : A ≤ 0 := by
      by_contra hn
      push Not at hn
      have := mul_pos hn (by positivity : 0 < σω / 4)
      linarith
    exact le_antisymm this hA0
  have hnorm : ‖lineProjection e₀ - lineProjection e‖ = 0 := by
    rw [hA] at hAz
    exact (pow_eq_zero_iff two_ne_zero).mp hAz
  exact (lineProjection_eq_iff_of_unit he₀ he).mp (sub_eq_zero.mp (norm_eq_zero.mp hnorm))

/-! ### HA9.d: mesoscopic absence of repeated layers -/

/-- **HA9.d, mesoscopic flatness.** For a compact value range `[a, b] ⊂ (0, 1)` and `η > 0` there
are `M, ℓ > 0` such that: if `U(X) ∈ [a, b]`, `d ≥ M` and the tilt of `U` along a unit vector `e`
on `B̄_d(X)` is below `ℓ dᵐ`, then every `X' ∈ B̄_d(X)` with `U(X') ∈ [a, b]` satisfies
`|⟪e, X' - X⟫| < η d`. -/
theorem RigidityHypotheses.exists_mesoscopic_flatness (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) {η : ℝ} (hη : 0 < η) :
    ∃ M ℓ : ℝ, 0 < M ∧ 0 < ℓ ∧ ∀ (X X' e : Space (m + 1)) (d : ℝ), ‖e‖ = 1 → M ≤ d →
      zeroExtension g u X ∈ Icc a b → zeroExtension g u X' ∈ Icc a b → ‖X' - X‖ ≤ d →
      ballTiltIntegral (zeroExtension g u) X e d < ℓ * d ^ m →
      |inner ℝ e (X' - X)| < η * d := by
  by_contra hcon
  simp only [not_exists, not_and, not_forall, not_lt] at hcon
  have hseq : ∀ j : ℕ, ∃ (X X' e : Space (m + 1)) (d : ℝ), ‖e‖ = 1 ∧ (j : ℝ) + 1 ≤ d ∧
      zeroExtension g u X ∈ Icc a b ∧ zeroExtension g u X' ∈ Icc a b ∧ ‖X' - X‖ ≤ d ∧
      ballTiltIntegral (zeroExtension g u) X e d < 1 / ((j : ℝ) + 1) * d ^ m ∧
      η * d ≤ |inner ℝ e (X' - X)| := by
    intro j
    obtain ⟨X, X', e, d, he, hd, hX, hX', hXX', ht, hfar⟩ :=
      hcon ((j : ℝ) + 1) (1 / ((j : ℝ) + 1)) (by positivity) (by positivity)
    exact ⟨X, X', e, d, he, hd, hX, hX', hXX', ht, hfar⟩
  choose X X' ev d hev hd hX hX' hXX' htilt hfar using hseq
  have hd1 : ∀ j, 1 ≤ d j := fun j ↦ le_trans (by
    have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    linarith) (hd j)
  have hdpos : ∀ j, 0 < d j := fun j ↦ zero_lt_one.trans_le (hd1 j)
  have hdt : Tendsto d atTop atTop := tendsto_atTop_mono hd
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  -- the halfspace limit at the centers `X j`
  obtain ⟨φ₁, hφ₁, e, he, hlocal⟩ := hr.exists_level_halfspace_subseq h hsharp ha hb X hX hd1 hdt
  -- compactness of the directions and of the rescaled second points
  set z : ℕ → Space (m + 1) := fun j ↦ (d j)⁻¹ • (X' j - X j) with hzdef
  have hz : ∀ j, z j ∈ closedBall (0 : Space (m + 1)) 1 := by
    intro j
    rw [mem_closedBall, dist_zero_right, hzdef, norm_smul, Real.norm_of_nonneg
      (inv_nonneg.mpr (hdpos j).le), inv_mul_le_iff₀ (hdpos j), mul_one]
    exact hXX' j
  have hcpt : IsCompact (sphere (0 : Space (m + 1)) 1 ×ˢ closedBall (0 : Space (m + 1)) 1) :=
    (isCompact_sphere 0 1).prod (isCompact_closedBall 0 1)
  obtain ⟨⟨e₀, z₀⟩, ⟨he₀m, hz₀⟩, φ₂, hφ₂, hconv⟩ := hcpt.tendsto_subseq
    (x := fun j ↦ (ev (φ₁ j), z (φ₁ j))) (fun j ↦ ⟨by simp [hev], hz _⟩)
  have he₀ : ‖e₀‖ = 1 := by simpa using he₀m
  have hconv_e : Tendsto (fun j ↦ ev (φ₁ (φ₂ j))) atTop (𝓝 e₀) := by
    have := (continuous_fst.tendsto _).comp hconv
    simpa [Function.comp_def] using this
  have hconv_z : Tendsto (fun j ↦ z (φ₁ (φ₂ j))) atTop (𝓝 z₀) := by
    have := (continuous_snd.tendsto _).comp hconv
    simpa [Function.comp_def] using this
  set φ := φ₁ ∘ φ₂ with hφdef
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  have hconv_z' : Tendsto (fun j ↦ z (φ j)) atTop (𝓝 z₀) := hconv_z
  have hlocal' : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (X (φ j) + d (φ j) • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) :=
    fun K hK ↦ (hlocal K hK).comp hφ₂.tendsto_atTop
  have hdt' : Tendsto (fun j ↦ d (φ j)) atTop atTop := hdt.comp hφ.tendsto_atTop
  -- the normalized tilt along `ev` vanishes
  have htilt' : Tendsto (fun j ↦ (d (φ j) ^ m)⁻¹ *
      ballTiltIntegral (zeroExtension g u) (X (φ j)) (ev (φ j)) (d (φ j))) atTop (𝓝 0) := by
    have hle : ∀ j, (d (φ j) ^ m)⁻¹ *
        ballTiltIntegral (zeroExtension g u) (X (φ j)) (ev (φ j)) (d (φ j)) ≤
          1 / ((φ j : ℝ) + 1) := by
      intro j
      have hdm : 0 < d (φ j) ^ m := pow_pos (hdpos _) m
      rw [inv_mul_le_iff₀ hdm]
      have := htilt (φ j)
      linarith [mul_comm (1 / ((φ j : ℝ) + 1)) (d (φ j) ^ m)]
    have hnn : ∀ j, 0 ≤ (d (φ j) ^ m)⁻¹ *
        ballTiltIntegral (zeroExtension g u) (X (φ j)) (ev (φ j)) (d (φ j)) := by
      intro j
      apply mul_nonneg (inv_nonneg.mpr (pow_nonneg (hdpos _).le m))
      exact setIntegral_nonneg measurableSet_closedBall fun y _ ↦ by
        have := abs_real_inner_le_norm (gradient (zeroExtension g u) y) (ev (φ j))
        rw [hev, mul_one] at this
        nlinarith [abs_nonneg (inner ℝ (gradient (zeroExtension g u) y) (ev (φ j))),
          sq_abs (inner ℝ (gradient (zeroExtension g u) y) (ev (φ j)))]
    have hto : Tendsto (fun j ↦ 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    exact squeeze_zero hnn hle hto
  -- the halfspace normal is `± e₀`
  have hnormal := hr.halfspace_normal_eq_or_neg_of_small_tilt h hsharp (X ∘ φ)
    (fun j ↦ hdpos _) he hlocal' (ev ∘ φ) (fun j ↦ hev _) he₀ hconv_e htilt'
  -- the second points stay a definite distance from the plane
  have hfar' : η ≤ |inner ℝ e₀ z₀| := by
    have hj : ∀ j, η ≤ |inner ℝ (ev (φ j)) (z (φ j))| := by
      intro j
      have h1 := hfar (φ j)
      have h2 : inner ℝ (ev (φ j)) (z (φ j)) =
          (d (φ j))⁻¹ * inner ℝ (ev (φ j)) (X' (φ j) - X (φ j)) := by
        rw [hzdef, inner_smul_right]
      rw [h2, abs_mul, abs_of_pos (inv_pos.mpr (hdpos _)), le_inv_mul_iff₀ (hdpos _)]
      linarith [mul_comm η (d (φ j))]
    have hcont : Tendsto (fun j ↦ |inner ℝ (ev (φ j)) (z (φ j))|) atTop
        (𝓝 |inner ℝ e₀ z₀|) := (hconv_e.inner hconv_z).abs
    exact ge_of_tendsto' hcont hj
  have hfare : η ≤ |inner ℝ e z₀| := by
    rcases hnormal with rfl | rfl
    · exact hfar'
    · rwa [inner_neg_left, abs_neg]
  have hpt : ∀ j, X (φ j) + d (φ j) • z (φ j) = X' (φ j) := by
    intro j
    rw [hzdef, smul_smul, mul_inv_cancel₀ (hdpos _).ne', one_smul, add_sub_cancel]
  set K := closedBall z₀ (η / 2) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hzK : ∀ᶠ j in atTop, z (φ j) ∈ K :=
    hconv_z'.eventually (closedBall_mem_nhds z₀ (by positivity))
  have hinner_near : ∀ x ∈ K, |inner ℝ e x - inner ℝ e z₀| ≤ η / 2 := by
    intro x hx
    rw [← inner_sub_right]
    calc |inner ℝ e (x - z₀)| ≤ ‖e‖ * ‖x - z₀‖ := abs_real_inner_le_norm _ _
      _ ≤ η / 2 := by
        rw [he, one_mul, ← dist_eq_norm]
        exact hx
  rcases le_or_gt 0 (inner ℝ e z₀) with hpos | hneg
  · -- the second points lie in the positive phase of the limit
    have hz0 : η ≤ inner ℝ e z₀ := by rwa [abs_of_nonneg hpos] at hfare
    have hKpos : ∀ x ∈ K, 0 < inner ℝ e x := by
      intro x hx
      have := (abs_le.mp (hinner_near x hx)).1
      linarith
    have hu := hr.translated_tendstoUniformlyOn_one_positive_halfspace h hsharp (X ∘ φ)
      (fun j ↦ hdpos _) hdt' he hlocal' hKc hKpos
    have h1 : Tendsto (fun j ↦ zeroExtension g u (X (φ j) + d (φ j) • z (φ j))) atTop (𝓝 1) := by
      have := hu.tendsto_comp (f := fun x : Space (m + 1) ↦ (1 : ℝ)) continuousWithinAt_const
        (tendsto_nhdsWithin_iff.mpr ⟨hconv_z', hzK⟩)
      exact this
    simp only [hpt] at h1
    have h2 : ∀ j, zeroExtension g u (X' (φ j)) ≤ b := fun j ↦ (hX' (φ j)).2
    have h3 : (1 : ℝ) ≤ b := le_of_tendsto' h1 h2
    linarith
  · -- the second points lie in the zero phase of the limit
    have hz0 : η ≤ -inner ℝ e z₀ := by rwa [abs_of_neg hneg] at hfare
    have hKneg : ∀ x ∈ K, inner ℝ e x < 0 := by
      intro x hx
      have := (abs_le.mp (hinner_near x hx)).2
      linarith
    have hev0 := hr.translated_eventually_eq_zero_negative_halfspace h hsharp (X ∘ φ)
      (fun j ↦ hdpos _) hdt' he hlocal' hKc hKneg
    obtain ⟨j, hj, hjK⟩ := (hev0.and hzK).exists
    have h1 := hj hjK
    simp only [Function.comp_apply, hpt, Pi.zero_apply] at h1
    have h2 := (hX' (φ j)).1
    linarith

end SerrinEpigraph
