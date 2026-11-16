module

public import SerrinEpigraph.PlaneTiltPhaseLimit

/-!
# Diffuse energy vanishes away from a planar phase limit
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- A thin normal cutoff can avoid a set separated from the plane while retaining
the full plane trace of a radial cutoff. -/
theorem exists_plane_cutoff_avoiding_set {m : ℕ}
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {e : Space (m + 1)}
    (hQ : Q (verticalDirection m) = e) {K : Set (Space (m + 1))}
    {δ t s : ℝ} (hδ : 0 < δ) (hgap : ∀ x ∈ K, δ ≤ |inner ℝ e x|)
    (ht : 0 < t) (hts : t < s) :
    ∃ ψ : Space (m + 1) → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ closedBall 0 s ∧ (∀ x, ψ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ K, ψ x = 0) ∧
      volume.real (closedBall (0 : Space m) t) ≤ ∫ y : Space m, ψ (Q (point y 0)) := by
  let η : ContDiffBump (0 : Space (m + 1)) := ⟨t, s, ht, hts⟩
  let χ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let ψ : Space (m + 1) → ℝ := fun x ↦ η x * χ (inner ℝ e x)
  have hψ : ContDiff ℝ 1 ψ := η.contDiff.mul (χ.contDiff.comp (innerSL ℝ e).contDiff)
  have hc : HasCompactSupport ψ := η.hasCompactSupport.mul_right
  have hs : tsupport ψ ⊆ closedBall 0 s := by
    have hh := tsupport_mul_subset_left (f := (η : Space (m + 1) → ℝ))
      (g := fun x ↦ χ (inner ℝ e x))
    simpa only [η.tsupport_eq] using hh
  refine ⟨ψ, hψ, hc, hs, ?_, ?_, ?_⟩
  · intro x
    exact ⟨mul_nonneg η.nonneg χ.nonneg,
      (mul_le_mul η.le_one χ.le_one χ.nonneg (by norm_num)).trans_eq (one_mul 1)⟩
  · intro x hx
    have hz : χ (inner ℝ e x) = 0 := χ.zero_of_le_dist
      (by simpa only [χ, Real.dist_eq, sub_zero] using hgap x hx)
    simp only [ψ, hz, mul_zero]
  · have hnormal (y : Space m) : inner ℝ e (Q (point y 0)) = 0 := by
      rw [← hQ, Q.inner_map_map]
      simp [verticalDirection, EuclideanSpace.inner_single_left, point]
    have hχ : χ (0 : ℝ) = 1 := χ.one_of_mem_closedBall (by simp [χ]; positivity)
    have htrace := plane_trace_integral_ge_ball_volume (η.continuous.comp Q.continuous)
      (η.hasCompactSupport.comp_homeomorph Q.toHomeomorph) (fun _ ↦ η.nonneg)
      (fun x hx ↦ η.one_of_mem_closedBall
        (by simpa only [mem_closedBall, dist_zero_right, Q.norm_map] using hx))
    simpa only [ψ, hnormal, hχ, mul_one, Function.comp_def] using htrace

/-- A compact set avoiding a linear hyperplane has a positive uniform normal gap. -/
theorem exists_normal_gap_of_compact {d : ℕ} {e : Space d} {K : Set (Space d)}
    (hK : IsCompact K) (havoid : ∀ x ∈ K, inner ℝ e x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ |inner ℝ e x| := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne
      (show ContinuousOn (fun x : Space d ↦ |inner ℝ e x|) K from
        (continuous_const.inner continuous_id).abs.continuousOn)
    exact ⟨|inner ℝ e x|, abs_pos.mpr (havoid x hx), hmin⟩
  · exact ⟨1, zero_lt_one, fun x hx ↦ (hne ⟨x, hx⟩).elim⟩

/-- A convergent sharp upper mass bound and phase convergence exclude residual energy
on every compact set disjoint from the limiting plane. -/
theorem integral_density_tendsto_zero_away_plane_of_mass_bound
    {m : ℕ} {v q : ℕ → Space (m + 1) → ℝ}
    (hv : ∀ j, LocallyLipschitz (v j)) {B : ℕ → ℝ}
    (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) (B j))
    (hiq : ∀ j K, IsCompact K → IntegrableOn (q j) K)
    (hgrad : ∀ j x, ‖gradient (v j) x‖ ≤ q j x)
    {σ : ℝ} (hσ : 0 ≤ σ) {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖v j x - {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ σ) x‖)
        atTop (𝓝 0))
    {A : ℕ → ℝ → ℝ}
    (hbound : ∀ j s, 0 < s → (∫ x in closedBall 0 s, q j x) ≤ A j s)
    (hmass : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ A j s) atTop
      (𝓝 (σ * (s ^ m * volume.real (closedBall (0 : Space m) 1)))))
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (havoid : ∀ x ∈ K, inner ℝ e x ≠ 0) :
    Tendsto (fun j ↦ ∫ x in K, q j x) atTop (𝓝 0) := by
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_vertical he
  obtain ⟨δ, hδ, hgap⟩ := exists_normal_gap_of_compact hK havoid
  obtain ⟨s₀, hs₀⟩ := hK.isBounded.subset_ball (0 : Space (m + 1))
  let s := |s₀| + 1
  have hs : 0 < s := by dsimp [s]; positivity
  have hKs : K ⊆ closedBall 0 s := by
    apply hs₀.trans
    exact (ball_subset_ball (by dsimp [s]; linarith [le_abs_self s₀])).trans ball_subset_closedBall
  let M : ℝ → ℝ := fun t ↦ σ * (t ^ m * volume.real (closedBall (0 : Space m) 1))
  have hM : Continuous M := by unfold M; fun_prop
  let t : ℕ → ℝ := fun n ↦ s - (s / 2) * (1 / ((n : ℝ) + 1))
  have ht (n : ℕ) : 0 < t n := by
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hh := mul_le_mul_of_nonneg_left hfrac (half_pos hs).le
    dsimp [t]
    linarith
  have hts (n : ℕ) : t n < s := sub_lt_self _ (mul_pos (half_pos hs) (by positivity))
  have hlimit : Tendsto t atTop (𝓝 s) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds (x := s)).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (s / 2))
  have hsmall : Tendsto (fun n ↦ M s - M (t n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self] using
      (tendsto_const_nhds (x := M s)).sub ((hM.tendsto s).comp hlimit)
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j ↦ ha.trans_le
      (integral_nonneg (fun x ↦ (norm_nonneg _).trans (hgrad j x))))
  · intro b hb
    obtain ⟨n, hn⟩ := (hsmall.eventually_lt_const (half_pos hb)).exists
    obtain ⟨ψ, hψ, hc, hsupp, hψval, hzero, htrace⟩ :=
      exists_plane_cutoff_avoiding_set Q hQ hδ hgap (ht n) (hts n)
    have htrace' : M (t n) ≤ σ * ∫ y : Space m, ψ (Q (point y 0)) := by
      have hh := mul_le_mul_of_nonneg_left htrace hσ
      rw [Measure.addHaar_real_closedBall' volume (0 : Space m) (ht n).le,
        finrank_euclideanSpace_fin] at hh
      exact hh
    have hE : MeasurableSet {y : Space (m + 1) | 0 < inner ℝ e y} :=
      (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
    have hp : IntegrableOn
        ({y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ σ)) (closedBall 0 s) :=
      (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 s)).indicator hE
    have hf := integral_cutoff_gradient_tendsto_of_integral_norm_sub_tendsto hv hval
      hψ hc (isCompact_closedBall 0 s) hsupp hp e (hlocal s hs)
    rw [integral_positive_halfspace_indicator_test Q hQ hψ hc measurableSet_closedBall
      hsupp σ, neg_mul, neg_neg] at hf
    have hu := (hmass s hs).sub hf
    have hlim : M s - σ * ∫ y : Space m, ψ (Q (point y 0)) < b := by linarith
    filter_upwards [hu.eventually_lt_const hlim] with j hj
    have hi := integral_density_le_mass_add_test_of_test_zero (hv j) (hval j) hψ hc
      hK (isCompact_closedBall 0 s) hKs hsupp hψval hzero he
      (hiq j _ (isCompact_closedBall 0 s)) (hgrad j)
    have hparts := setIntegral_inner_gradient_mul_eq_neg_of_locallyLipschitz
      (hv j) (hval j) hψ hc (isCompact_closedBall 0 s) hsupp e
    have hbA := hbound j s hs
    linarith

/-- Exact planar total mass and phase convergence exclude residual energy on every
compact set disjoint from the limiting plane. -/
theorem integral_density_tendsto_zero_away_plane
    {m : ℕ} {v q : ℕ → Space (m + 1) → ℝ}
    (hv : ∀ j, LocallyLipschitz (v j)) {B : ℕ → ℝ}
    (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) (B j))
    (hiq : ∀ j K, IsCompact K → IntegrableOn (q j) K)
    (hgrad : ∀ j x, ‖gradient (v j) x‖ ≤ q j x)
    {σ : ℝ} (hσ : 0 ≤ σ) {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖v j x - {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ σ) x‖)
        atTop (𝓝 0))
    (hmass : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s, q j x) atTop
      (𝓝 (σ * (s ^ m * volume.real (closedBall (0 : Space m) 1)))))
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (havoid : ∀ x ∈ K, inner ℝ e x ≠ 0) :
    Tendsto (fun j ↦ ∫ x in K, q j x) atTop (𝓝 0) :=
  integral_density_tendsto_zero_away_plane_of_mass_bound hv hval hiq hgrad hσ he
    hlocal (fun _ _ _ ↦ le_rfl) hmass hK havoid

/-- CO6 for the actual Serrin solution: every compact set disjoint from the plane
has vanishing rescaled diffuse energy along the planar phase sequence. -/
theorem RigidityHypotheses.rescaled_energy_tendsto_zero_away_plane
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (havoid : ∀ x ∈ K, inner ℝ e x ≠ 0) :
    Tendsto (fun j ↦ ∫ x in K,
      rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x)
        atTop (𝓝 0) := by
  have hU (j : ℕ) : LocallyLipschitz (fun x ↦ zeroExtension g u (R j • x)) :=
    h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
  have hval (j : ℕ) (x : Space (m + 1)) : zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hE : MeasurableSet {y : Space (m + 1) | 0 < inner ℝ e y} :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
  apply integral_density_tendsto_zero_away_plane
    (fun j ↦ (hr.phasePrimitive_zeroExtension_locallyLipschitz h).comp
      (lipschitzWith_smul (R j)).locallyLipschitz)
    (B := fun _ ↦ phasePrimitive f 1)
    (fun j x ↦ h.phasePrimitive_mem_Icc (hval j x))
    (fun j _ hK ↦ h.integrableOn_rescaledPhaseEnergy (hU j) (hval j) (R j) hK)
    (fun j x ↦ hr.rescaledPrimitive_gradient_le_energy h (zero_lt_one.trans_le (hR j)) x)
    (hr.phasePrimitive_one_pos h).le he
    (fun s _ ↦ hr.primitive_local_limit_of_phase_local_limit h R hE
      (isCompact_closedBall 0 s) (hlocal _ (isCompact_closedBall 0 s)))
    _ hK havoid
  intro s hs
  simpa only [Function.comp_def, mul_assoc, mul_left_comm, mul_comm] using
    (hr.rescaled_energy_tendsto_of_positive_halfspace_limit h hR hRt he hlocal hs).comp hRt

end SerrinEpigraph
