module

public import SerrinEpigraph.TiltExcessStep

/-!
# Tilt-excess decay (`GR12`)

* `IsFlatConfig b E Ω μ ν`: a normalized configuration through the origin — `E` is a local
  perimeter minimizer in `Ω`, `(μ, ν)` is a slab-trapped representation of its perimeter over
  `B_2 × (-1, 1) ⊆ Ω` (trapped in `|t| ≤ 1/2`), and `0 ∈ ∂E`.
* `IsFlatConfig.exists_decay_of_excess_eq_zero`: zero excess propagates to the next scale.
* `exists_tilt_decay` (**`GR12.2`**): there are `0 < θ ≤ 1/10`, a threshold `η₀ > 0` and a
  constant `C` such that every flat configuration with excess `e ≤ η₀` admits a linear isometry
  `Q` with `‖Q e_n - e_n‖ ≤ C √e` for which the configuration `{x | θ Q x ∈ E}` is again flat
  with excess at most `e/2`. The proof is the compactness argument of `GR12`: along a violating
  sequence with `e_j → 0`, `GR11` gives a harmonic limit `z`; the Householder frame of its
  first-order Taylor polynomial and the tilted `GR8.2` (`IsLocalPerimeterMinimizer.tilt_step`)
  give the decay through the harmonic Taylor estimate.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal NNReal Laplacian

namespace SerrinEpigraph

/-- A normalized flat configuration through the origin. -/
structure IsFlatConfig {m : ℕ} (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (E Ω : Set (Space (m + 1))) (μ : Measure (Space (m + 1)))
    (ν : Space (m + 1) → Space (m + 1)) : Prop where
  min : IsLocalPerimeterMinimizer b E Ω
  slab : SlabTrappedRepresentation b E (ball (0 : Space m) 2) (1 / 2) 1 μ ν
  cyl : cylinderSet (ball (0 : Space m) 2) 1 ⊆ Ω
  zero_mem : (0 : Space (m + 1)) ∈ measureTheoreticBoundary E

theorem similarity_zero_apply_zero {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (θ : ℝ) :
    similarity Q 0 θ 0 = 0 := by
  simp [similarity]

theorem zero_mem_measureTheoreticBoundary_preimage_similarity {d : ℕ} {E : Set (Space d)}
    (h0 : (0 : Space d) ∈ measureTheoreticBoundary E) (Q : Space d ≃ₗᵢ[ℝ] Space d) {θ : ℝ}
    (hθ : 0 < θ) : (0 : Space d) ∈ measureTheoreticBoundary (similarity Q 0 θ ⁻¹' E) := by
  rw [measureTheoreticBoundary_preimage_similarity E Q 0 hθ, mem_preimage,
    similarity_zero_apply_zero]
  exact h0

/-- The cutoff `η = 1` on `B_{4θ}`, supported in `B̄_{9θ/2}`. -/
def decayCutoff {m : ℕ} {θ : ℝ} (hθ : 0 < θ) : ContDiffBump (0 : Space m) where
  rIn := 4 * θ
  rOut := 9 * θ / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem decayCutoff_props {m : ℕ} {θ : ℝ} (hθ : 0 < θ) :
    ContDiff ℝ 1 (decayCutoff (m := m) hθ : Space m → ℝ) ∧
      HasCompactSupport (decayCutoff (m := m) hθ : Space m → ℝ) ∧
      (∀ y, 0 ≤ (decayCutoff (m := m) hθ : Space m → ℝ) y) ∧
      (∀ y, (decayCutoff (m := m) hθ : Space m → ℝ) y ≤ 1) ∧
      (∀ y ∈ ball (0 : Space m) (4 * θ), (decayCutoff (m := m) hθ : Space m → ℝ) y = 1) ∧
      tsupport (decayCutoff (m := m) hθ : Space m → ℝ) ⊆ ball 0 (5 * θ) := by
  set B := decayCutoff (m := m) hθ
  refine ⟨B.contDiff, B.hasCompactSupport, fun y ↦ B.nonneg, fun y ↦ B.le_one,
    fun y hy ↦ B.one_of_mem_closedBall (ball_subset_closedBall hy), ?_⟩
  rw [B.tsupport_eq]
  exact closedBall_subset_ball (show B.rOut < 5 * θ by
    show 9 * θ / 2 < 5 * θ
    linarith)

namespace IsFlatConfig

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}

/-- **The tilt step produces a flat configuration.** -/
theorem tilt_step (hF : IsFlatConfig b E Ω μ ν) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 10)
    {c δ : ℝ} (hcδ : |c| ≤ δ) (hδθ : δ ≤ θ / 16)
    (hphase : ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      |x (Fin.last m)| < 1 → δ < |x (Fin.last m) - c| → (x ∈ E ↔ c < x (Fin.last m)))
    {p : Space m} {a s : ℝ} (hs : 0 ≤ s) (hsp : s * ‖p‖ ≤ 1 / 40) :
    IsFlatConfig b (similarity (tiltFrame p s) 0 θ ⁻¹' E) (similarity (tiltFrame p s) 0 θ ⁻¹' Ω)
        ((similarityMeasure μ (tiltFrame p s) 0 θ).restrict (cylinderSet (ball (0 : Space m) 2) 1))
        (fun x ↦ (tiltFrame p s).symm (ν (similarity (tiltFrame p s) 0 θ x))) ∧
      (projectedExcessMeasure ((similarityMeasure μ (tiltFrame p s) 0 θ).restrict
          (cylinderSet (ball (0 : Space m) 2) 1))
          (fun x ↦ (tiltFrame p s).symm (ν (similarity (tiltFrame p s) 0 θ x)))).real
          (ball 0 2) ≤
        (θ ^ m)⁻¹ * (flatteningConstant / θ ^ 2) *
          ∫ x, (decayCutoff (m := m) hθ0 : Space m → ℝ) (horizontal x) *
            (x (Fin.last m) - (c + s * (a + inner ℝ p (horizontal x)))) ^ 2 ∂μ := by
  obtain ⟨hη, hηc, hη0, -, hη1, -⟩ := decayCutoff_props (m := m) hθ0
  obtain ⟨h1, h2, h3, h4⟩ := hF.min.tilt_step hF.slab hF.cyl hθ0 hθ1 hcδ hδθ hphase hs hsp
    (a := a) hη hηc hη0 hη1
  exact ⟨⟨h1, h2, h3, zero_mem_measureTheoreticBoundary_preimage_similarity hF.zero_mem _ hθ0⟩,
    h4⟩

/-- **Zero excess propagates.** -/
theorem exists_decay_of_excess_eq_zero (hF : IsFlatConfig b E Ω μ ν)
    (he : (projectedExcessMeasure μ ν).real (ball 0 2) = 0) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1 / 10) :
    ∃ μ' ν', IsFlatConfig b (similarity (tiltFrame (0 : Space m) 0) 0 θ ⁻¹' E)
        (similarity (tiltFrame (0 : Space m) 0) 0 θ ⁻¹' Ω) μ' ν' ∧
      (projectedExcessMeasure μ' ν').real (ball 0 2) ≤ 0 := by
  have hS := hF.slab
  have hband := hF.min.gr10_band_width hS subset_rfl hF.cyl (by rw [he]; norm_num)
    (r₀ := 1 / 4) (by norm_num) le_rfl (by norm_num)
    (by
      rw [he, Real.sqrt_zero]
      simp only [mul_zero, add_zero]
      have := minimizerVolumeDensityConst_pos m
      positivity)
  rw [he, Real.sqrt_zero] at hband
  simp only [mul_zero, add_zero, zero_div] at hband
  have hq : ((1 : ℝ) / (m + 1)) ≠ 0 := by positivity
  rw [Real.zero_rpow hq] at hband
  set a := ⨍ z in ball (0 : Space m) 1, columnSignedHeight E (1 / 2) z with ha_def
  have ha0 : a = 0 := by
    have h := hband.2 0 hF.zero_mem (by rw [horizontal_zero]; exact mem_ball_self (by norm_num))
      (by simp)
    simpa using h
  have hband0 : ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      |x (Fin.last m)| < 1 → |x (Fin.last m) - 0| ≤ 0 := by
    intro x hx hxh hxn
    have := hband.2 x hx hxh hxn
    rwa [ha0] at this
  have hphase := hS.ae_mem_iff_of_band (convex_ball (0 : Space m) (1 / 2))
    (ball_subset_ball (by norm_num)) (a := 0) (δ := 0) (by norm_num) le_rfl hband0
  obtain ⟨hF', hexc⟩ := hF.tilt_step hθ0 hθ1 (c := 0) (δ := 0) (by simp) (by positivity) hphase
    (p := 0) (a := 0) (s := 0) le_rfl (by simp)
  refine ⟨_, _, hF', hexc.trans (le_of_eq ?_)⟩
  have hint : ∫ x, (decayCutoff (m := m) hθ0 : Space m → ℝ) (horizontal x) *
      (x (Fin.last m) - (0 + 0 * (0 + inner ℝ (0 : Space m) (horizontal x)))) ^ 2 ∂μ = 0 := by
    obtain ⟨-, -, -, -, -, hsupp⟩ := decayCutoff_props (m := m) hθ0
    apply integral_eq_zero_of_ae
    filter_upwards [hS.ae_abs_last_le] with x hx
    by_cases hη : (decayCutoff (m := m) hθ0 : Space m → ℝ) (horizontal x) = 0
    · simp [hη]
    · have hxB : horizontal x ∈ ball (0 : Space m) (1 / 2) :=
        ball_subset_ball (by linarith) (hsupp (subset_tsupport _ hη))
      have h := hband0 x hx.1 hxB (abs_lt.mpr hx.2.1.2)
      have hx0 : x (Fin.last m) = 0 := by
        have := abs_nonneg (x (Fin.last m) - 0)
        have h' : |x (Fin.last m) - 0| = 0 := le_antisymm h this
        simpa using h'
      simp [hx0]
  rw [hint, mul_zero]

end IsFlatConfig

/-- A bound for `‖∇z(0)‖` of the harmonic limits of `GR11`. -/
def tiltConst (m : ℕ) : ℝ := harmonicGradConst m * Real.sqrt (gr11L2Const m)

theorem tiltConst_nonneg (m : ℕ) : 0 ≤ tiltConst m :=
  mul_nonneg harmonicGradConst_nonneg (Real.sqrt_nonneg _)

theorem gr11L2Const_nonneg (m : ℕ) : 0 ≤ gr11L2Const m := by
  have := SlabTrappedRepresentation.gradApproxConst_nonneg m
  unfold gr11L2Const
  positivity

/-- The decay ratio of `GR12`. -/
def decayTheta (m : ℕ) : ℝ :=
  min (1 / 10) (1 / (16 * flatteningConstant * harmonicTaylorExcessConst m * 5 ^ (m + 4) *
    gr11L2Const m + 1))

theorem decayTheta_pos (m : ℕ) : 0 < decayTheta m := by
  have := flatteningConstant_pos
  have := harmonicTaylorExcessConst_nonneg (d := m)
  have := gr11L2Const_nonneg m
  unfold decayTheta
  exact lt_min (by norm_num) (by positivity)

theorem decayTheta_le (m : ℕ) : decayTheta m ≤ 1 / 10 := min_le_left _ _

/-- The decay inequality: `4 F C_T 5^{m+4} C_L θ² ≤ 1/4`. -/
theorem decayTheta_sq_le (m : ℕ) :
    4 * flatteningConstant * harmonicTaylorExcessConst m * 5 ^ (m + 4) * gr11L2Const m *
      decayTheta m ^ 2 ≤ 1 / 4 := by
  have hF := flatteningConstant_pos
  have hT := harmonicTaylorExcessConst_nonneg (d := m)
  have hL := gr11L2Const_nonneg m
  set K := 16 * flatteningConstant * harmonicTaylorExcessConst m * 5 ^ (m + 4) * gr11L2Const m
    with hK
  have hK0 : 0 ≤ K := by positivity
  set θ := decayTheta m with hθ_def
  have hθ0 : 0 < θ := decayTheta_pos m
  have hθ1 : θ ≤ 1 / 10 := decayTheta_le m
  have hθK : θ ≤ 1 / (K + 1) := min_le_right _ _
  have hθK' : θ * (K + 1) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hθK
    exact hθK
  have hKθ : K * θ ^ 2 ≤ 1 := by nlinarith
  have heq : 4 * flatteningConstant * harmonicTaylorExcessConst m * 5 ^ (m + 4) *
      gr11L2Const m * θ ^ 2 = K * θ ^ 2 / 4 := by
    rw [hK]
    ring
  rw [heq]
  linarith

/-- **`GR12.2`: tilt-excess decay.** There is a threshold `η₀ > 0` such that every flat
configuration with excess `e ≤ η₀` admits a linear isometry `Q` with
`‖Q e_n - e_n‖ ≤ tiltConst m · √e` for which `{x | θ Q x ∈ E}` (with `θ = decayTheta m`) is again
a flat configuration, with excess at most `e/2`. -/
theorem exists_tilt_decay (m : ℕ) (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (E Ω : Set (Space (m + 1))) (μ : Measure (Space (m + 1)))
      (ν : Space (m + 1) → Space (m + 1)), IsFlatConfig b E Ω μ ν →
      (projectedExcessMeasure μ ν).real (ball 0 2) ≤ η₀ →
      ∃ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ‖Q (verticalDirection m) - verticalDirection m‖ ≤
          tiltConst m * Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) ∧
        ∃ μ' ν', IsFlatConfig b (similarity Q 0 (decayTheta m) ⁻¹' E)
            (similarity Q 0 (decayTheta m) ⁻¹' Ω) μ' ν' ∧
          (projectedExcessMeasure μ' ν').real (ball 0 2) ≤
            (projectedExcessMeasure μ ν).real (ball 0 2) / 2 := by
  set θ := decayTheta m with hθ_def
  have hθ0 : 0 < θ := decayTheta_pos m
  have hθ1 : θ ≤ 1 / 10 := decayTheta_le m
  have hF0 := flatteningConstant_pos
  by_contra hcon
  push Not at hcon
  choose E Ω μ ν hF he hbad using fun j : ℕ ↦ hcon (1 / ((j : ℝ) + 1)) (by positivity)
  set e : ℕ → ℝ := fun j ↦ (projectedExcessMeasure (μ j) (ν j)).real (ball (0 : Space m) 2)
    with he_def
  have he0 : ∀ j, 0 ≤ e j := fun j ↦ measureReal_nonneg
  -- violating configurations have positive excess
  have hpos : ∀ j, 0 < e j := by
    intro j
    rcases (he0 j).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨μ', ν', hF', he'⟩ := (hF j).exists_decay_of_excess_eq_zero h.symm hθ0 hθ1
      have hQ : ‖tiltFrame (0 : Space m) 0 (verticalDirection m) - verticalDirection m‖ ≤
          tiltConst m * Real.sqrt (e j) := by
        rw [tiltFrame_verticalDirection, norm_sub_rev]
        refine (norm_verticalDirection_sub_tiltNormal_le (0 : Space m) le_rfl).trans ?_
        rw [zero_mul]
        exact mul_nonneg (tiltConst_nonneg m) (Real.sqrt_nonneg _)
      have := hbad j _ hQ μ' ν' hF'
      have h0 : (projectedExcessMeasure (μ j) (ν j)).real (ball (0 : Space m) 2) = 0 := h.symm
      rw [h0] at this
      linarith
  have hlim : Tendsto e atTop (𝓝 0) :=
    squeeze_zero he0 he tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, z, c, δ, hzC, hzΔ, hL2, hc, hδ, hband, hphase, h111⟩ :=
    IsLocalPerimeterMinimizer.gr11_harmonic_limit (fun j ↦ (hF j).min) (fun j ↦ (hF j).slab)
      (fun j ↦ (hF j).cyl) (fun j ↦ (hF j).zero_mem) hpos hlim
  -- the first-order Taylor polynomial of the harmonic limit
  set a := z 0 with ha_def
  set p : Space m := (toDual ℝ (Space m)).symm (fderiv ℝ z 0) with hp_def
  have hpy : ∀ y, inner ℝ p y = fderiv ℝ z 0 y := fun y ↦ toDual_symm_apply
  have hp : ‖p‖ ≤ tiltConst m := by
    rw [hp_def, LinearIsometryEquiv.norm_map]
    have hg := norm_fderiv_le_of_harmonic isOpen_ball hzC hzΔ (x := 0) (r := 1)
      (closedBall_subset_ball (by norm_num)) one_pos
    rw [Real.one_rpow, mul_one, ← Real.sqrt_eq_rpow] at hg
    exact hg.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hL2) harmonicGradConst_nonneg)
  -- the cutoff and the Taylor estimate
  obtain ⟨hη, hηc, hη0, hη1, hηB, hηs⟩ := decayCutoff_props (m := m) hθ0
  set η : Space m → ℝ := (decayCutoff (m := m) hθ0 : Space m → ℝ) with hη_def
  have hηB' : tsupport η ⊆ ball 0 (1 / 2) := hηs.trans (ball_subset_ball (by linarith))
  have hTaylor : ∫ y, η y * (z y - (a + inner ℝ p y)) ^ 2 ≤
      harmonicTaylorExcessConst m * (5 * θ) ^ (m + 4) * gr11L2Const m := by
    have hT := harmonic_taylor_excess_le isOpen_ball hzC hzΔ (x := 0) (r := 1)
      (closedBall_subset_ball (by norm_num)) one_pos (θ := 5 * θ) (by positivity) (by linarith)
    rw [mul_one] at hT
    have hzc : ContinuousOn z (closedBall 0 (5 * θ)) :=
      hzC.continuousOn.mono (closedBall_subset_ball (by linarith))
    have hint : IntegrableOn (fun y ↦ (z y - z 0 - fderiv ℝ z 0 (y - 0)) ^ 2) (ball 0 (5 * θ)) :=
      ((((hzc.sub continuousOn_const).sub ((fderiv ℝ z 0).continuous.comp
        (continuous_id.sub continuous_const)).continuousOn).pow 2).integrableOn_compact
        (isCompact_closedBall 0 (5 * θ))).mono_set ball_subset_closedBall
    have hle : ∫ y, η y * (z y - (a + inner ℝ p y)) ^ 2 ≤
        ∫ y in ball (0 : Space m) (5 * θ), (z y - z 0 - fderiv ℝ z 0 (y - 0)) ^ 2 := by
      rw [← integral_indicator measurableSet_ball]
      refine integral_mono_of_nonneg (Eventually.of_forall fun y ↦ mul_nonneg (hη0 y)
        (sq_nonneg _)) (hint.integrable_indicator measurableSet_ball)
        (Eventually.of_forall fun y ↦ ?_)
      by_cases hy : y ∈ ball (0 : Space m) (5 * θ)
      · dsimp only
        rw [indicator_of_mem hy, sub_zero, ← hpy, ha_def]
        have h1 : z y - (z 0 + inner ℝ p y) = z y - z 0 - inner ℝ p y := by ring
        rw [h1]
        exact mul_le_of_le_one_left (sq_nonneg _) (hη1 y)
      · have hη0' : η y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hηs h))
        dsimp only
        rw [indicator_of_notMem hy, hη0', zero_mul]
    refine hle.trans (hT.trans ?_)
    exact mul_le_mul_of_nonneg_left hL2 (mul_nonneg harmonicTaylorExcessConst_nonneg
      (by positivity))
  -- the choice of `ε`
  set ε : ℝ := θ ^ (m + 2) / (4 * flatteningConstant) with hε_def
  have hε : 0 < ε := by positivity
  have hev := h111 η hη hηc hηB' hη0 hη1 a p ε hε
  -- eventually all smallness conditions hold
  have hsqrt : Tendsto (fun j ↦ Real.sqrt (e (φ j))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (hlim.comp hφ.tendsto_atTop)
    rw [Real.sqrt_zero] at this
    exact this
  have hsp_ev : ∀ᶠ j in atTop, Real.sqrt (e (φ j)) * ‖p‖ ≤ 1 / 40 := by
    have := hsqrt.mul_const ‖p‖
    rw [zero_mul] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  have hδ_ev : ∀ᶠ j in atTop, δ j ≤ θ / 16 := hδ.eventually (ge_mem_nhds (by positivity))
  obtain ⟨j, hj⟩ := (hev.and (hband.and (hphase.and (hsp_ev.and hδ_ev)))).exists
  obtain ⟨hj1, hj2, hj3, hj4, hj5⟩ := hj
  -- the band at the origin gives `|c j| ≤ δ j`
  have hcδ : |c j| ≤ δ j := by
    have h := hj2 0 (hF (φ j)).zero_mem
      (by rw [horizontal_zero]; exact mem_ball_self (by norm_num)) (by simp)
    simpa using h
  set s := Real.sqrt (e (φ j)) with hs_def
  obtain ⟨hF', hexc⟩ := (hF (φ j)).tilt_step hθ0 hθ1 hcδ hj5 hj3 (Real.sqrt_nonneg _) hj4
    (a := a)
  have hQ : ‖tiltFrame p s (verticalDirection m) - verticalDirection m‖ ≤
      tiltConst m * Real.sqrt (e (φ j)) := by
    rw [tiltFrame_verticalDirection, norm_sub_rev]
    refine (norm_verticalDirection_sub_tiltNormal_le p (Real.sqrt_nonneg _)).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg _)
  have hcontra := hbad (φ j) _ hQ _ _ hF'
  -- the excess estimate
  have hfac : 0 ≤ (θ ^ m)⁻¹ * (flatteningConstant / θ ^ 2) := by positivity
  have hbound : (projectedExcessMeasure ((similarityMeasure (μ (φ j)) (tiltFrame p s) 0 θ).restrict
      (cylinderSet (ball (0 : Space m) 2) 1))
      (fun x ↦ (tiltFrame p s).symm (ν (φ j) (similarity (tiltFrame p s) 0 θ x)))).real
      (ball 0 2) ≤ e (φ j) / 2 := by
    refine hexc.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hj1 hfac
    refine h1.trans ?_
    have hX : 4 * (∫ y, η y * (z y - (a + inner ℝ p y)) ^ 2) + ε ≤
        4 * (harmonicTaylorExcessConst m * (5 * θ) ^ (m + 4) * gr11L2Const m) + ε := by
      linarith [hTaylor]
    have h2 : (θ ^ m)⁻¹ * (flatteningConstant / θ ^ 2) *
        (4 * (harmonicTaylorExcessConst m * (5 * θ) ^ (m + 4) * gr11L2Const m) + ε) =
        4 * flatteningConstant * harmonicTaylorExcessConst m * 5 ^ (m + 4) * gr11L2Const m *
          θ ^ 2 + 1 / 4 := by
      rw [hε_def, mul_pow, pow_add, pow_add]
      field_simp
      ring
    have h3 := decayTheta_sq_le m
    rw [← hθ_def] at h3
    calc (θ ^ m)⁻¹ * (flatteningConstant / θ ^ 2) *
          (e (φ j) * (4 * (∫ y, η y * (z y - (a + inner ℝ p y)) ^ 2) + ε))
        = e (φ j) * ((θ ^ m)⁻¹ * (flatteningConstant / θ ^ 2) *
          (4 * (∫ y, η y * (z y - (a + inner ℝ p y)) ^ 2) + ε)) := by ring
      _ ≤ e (φ j) * ((θ ^ m)⁻¹ * (flatteningConstant / θ ^ 2) *
          (4 * (harmonicTaylorExcessConst m * (5 * θ) ^ (m + 4) * gr11L2Const m) + ε)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hfac) (he0 _)
      _ ≤ e (φ j) * (1 / 4 + 1 / 4) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left (by linarith) (he0 _)
      _ = e (φ j) / 2 := by ring
  linarith

end SerrinEpigraph
