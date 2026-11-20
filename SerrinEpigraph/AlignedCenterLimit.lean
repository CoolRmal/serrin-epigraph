module

public import SerrinEpigraph.AlignedHeightCompactness

/-!
# (B1) The centers of an aligned height limit tend to zero

This module proves the first conjunct of `HasAlignedHeightMoments`
(`SerrinEpigraph.AlignedHeightDecomposition`): for height-limit data along an aligned sequence, the
centers `a_j = ⨍_{B_ρ} h̃_j` (averages of the extended level heights) tend to `0`
(`RigidityHypotheses.tendsto_alignedCenter_zero`).

## Parameter conditions

`0 < ℓ`, `0 ≤ b < 1`, `0 < ρ`, `0 < τ`, `0 < s₁`, `s₂ < 1` and `ρ + |r₀| < 2`. These follow from the
conditions of (A) (`RigidityHypotheses.hasAlignedHeightCompactness_of_levelStructure`).

## Proof

Neither the cone condition, nor the slope bound, nor the Sobolev bound is needed. Fix `ε' > 0`.
* (*thin layers*, HA8) Eventually every point of `B̄_{ρ+τ}` with value in `[s₁, s₂]` lies in
  `|t| < ε'`. A slab level height `slabLevelHeight v τ s y` over `|y| < ρ` is either a crossing
  `t ∈ (-τ, τ)` of the level `s`, hence `|t| < ε'`, or the default value `0`
  (`abs_slabLevelHeight_lt`).
* (*McShane*) On the good set `D`, the McShane extension of heights bounded by `ε'` is bounded by
  `ε'` (it is at most the height itself and at least `-ε'`), and the extended height is always in
  `[-τ, τ]` (`abs_extendedHeight_le_of_mem`). Hence
  `|a_j| ≤ ε' + τ |B_ρ \ D_j| / |B_ρ|` (`abs_setAverage_extendedHeight_le_of_bound`).
* (*bad volume*, HA1.2) `|B_ρ \ D_j| ≲ ℓ⁻¹ ∫_{B̄_{ρ+η+|r₀|}} ε |∇_y v_j|² ≤ ℓ⁻¹ 2ᵐ δ_j² → 0`, using
  the cylinder normalization `𝓔(2, e_n) = δ_j²` and `ρ + η + |r₀| < 2`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal ENNReal

namespace SerrinEpigraph

/-! ### Bounds on the extended heights -/

/-- Under thin layers, the slab level heights over `B_ρ` are small: if every point of
`B̄_{ρ+τ}` with value in `[s₁, s₂]` has vertical coordinate less than `ε'` in absolute value, then
so does every slab level height of a level in `[s₁, s₂]` over `B_ρ` (it is either such a crossing
or the default value `0`). -/
theorem abs_slabLevelHeight_lt {m : ℕ} {v : Space (m + 1) → ℝ} {ρ τ s₁ s₂ ε' : ℝ}
    (hε' : 0 < ε')
    (hlev : ∀ z ∈ closedBall (0 : Space (m + 1)) (ρ + τ), v z ∈ Icc s₁ s₂ →
      |z (Fin.last m)| < ε')
    {s : ℝ} (hs : s ∈ Icc s₁ s₂) {y : Space m} (hy : y ∈ ball (0 : Space m) ρ) :
    |slabLevelHeight v τ s y| < ε' := by
  by_cases hex : ∃ t ∈ Ioo (-τ) τ, v (point y t) = s
  · obtain ⟨ht, hval⟩ := slabLevelHeight_spec hex
    have hz : point y (slabLevelHeight v τ s y) ∈ closedBall (0 : Space (m + 1)) (ρ + τ) := by
      rw [mem_closedBall, dist_zero_right]
      have h1 := norm_point_le y (slabLevelHeight v τ s y)
      have h2 : ‖y‖ < ρ := by simpa using hy
      have h3 : |slabLevelHeight v τ s y| < τ := abs_lt.mpr ⟨ht.1, ht.2⟩
      linarith
    have h4 := hlev _ hz (by rw [hval]; exact hs)
    rwa [last_point] at h4
  · unfold slabLevelHeight
    rw [dite_eq_right hex, abs_zero]
    exact hε'

/-- If the heights of a level `σ ∈ [s₁, s₂]` are at most `ε' ≤ τ` in absolute value on `D`, then
so is the extended height on `D`: the McShane extension is at most the height itself on `D` and
at least `-ε'` everywhere. -/
theorem abs_extendedHeight_le_of_mem {m : ℕ} {D : Set (Space m)} {L : ℝ≥0}
    {τ s₁ s₂ σ ε' : ℝ} {h : ℝ → Space m → ℝ} (hσ : σ ∈ Icc s₁ s₂) (hε'τ : ε' ≤ τ)
    (hh : ∀ z ∈ D, |h σ z| ≤ ε') {y : Space m} (hy : y ∈ D) :
    |extendedHeight D L τ s₁ s₂ h σ y| ≤ ε' := by
  unfold extendedHeight
  rw [clampLevel_eq hσ]
  have hbdd : BddBelow (range fun z : D ↦ h σ z + (L : ℝ) * dist y (z : Space m)) := by
    refine ⟨-ε', ?_⟩
    rintro w ⟨z, rfl⟩
    have h1 := (abs_le.mp (hh z z.2)).1
    have h2 : 0 ≤ (L : ℝ) * dist y (z : Space m) := mul_nonneg L.coe_nonneg dist_nonneg
    dsimp only
    linarith
  have hup : mcShaneExtension D L (h σ) y ≤ h σ y :=
    calc mcShaneExtension D L (h σ) y ≤ h σ y + L * dist y y := ciInf_le hbdd ⟨y, hy⟩
      _ = h σ y := by rw [dist_self, mul_zero, add_zero]
  have hlow : -ε' ≤ mcShaneExtension D L (h σ) y := by
    have : Nonempty D := ⟨⟨y, hy⟩⟩
    refine le_ciInf fun z ↦ ?_
    have h1 := (abs_le.mp (hh z z.2)).1
    have h2 : 0 ≤ (L : ℝ) * dist y (z : Space m) := mul_nonneg L.coe_nonneg dist_nonneg
    linarith
  have hyb := (abs_le.mp (hh y hy)).2
  have hmem : mcShaneExtension D L (h σ) y ∈ Icc (-τ) τ := ⟨by linarith, by linarith⟩
  rw [slabClamp_eq_of_mem hmem, abs_le]
  exact ⟨hlow, hup.trans hyb⟩

/-- **The average of an extended height.** If the heights of a level `σ ∈ [s₁, s₂]` are at most
`ε' ∈ [0, τ]` in absolute value on a measurable `D`, then the average of the extended height
over `B_ρ` is at most `ε' + τ |B_ρ \ D| / |B_ρ|` in absolute value. -/
theorem abs_setAverage_extendedHeight_le_of_bound {m : ℕ} {D : Set (Space m)}
    (hDm : MeasurableSet D)
    {L : ℝ≥0} {τ s₁ s₂ σ ε' ρ : ℝ} {h : ℝ → Space m → ℝ} (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (hσ : σ ∈ Icc s₁ s₂) (hε' : 0 ≤ ε') (hε'τ : ε' ≤ τ) (hh : ∀ z ∈ D, |h σ z| ≤ ε') :
    |⨍ z in ball (0 : Space m) ρ, extendedHeight D L τ s₁ s₂ h σ z| ≤
      ε' + τ * volume.real (ball (0 : Space m) ρ \ D) / volume.real (ball (0 : Space m) ρ) := by
  set B := ball (0 : Space m) ρ with hB
  set F := extendedHeight D L τ s₁ s₂ h σ with hF
  have hBpos : 0 < volume.real B :=
    ENNReal.toReal_pos (measure_ball_pos volume _ hρ).ne' measure_ball_lt_top.ne
  have hFc : Continuous F := (extendedHeight_lipschitzWith_of_any D L τ s₁ s₂ h σ).continuous
  have hFi : IntegrableOn F B :=
    (hFc.continuousOn.integrableOn_compact (isCompact_closedBall 0 ρ)).mono_set
      ball_subset_closedBall
  have hsplit : ∫ z in B, F z = (∫ z in B ∩ D, F z) + ∫ z in B \ D, F z :=
    (integral_inter_add_sdiff hDm hFi).symm
  have h1 : ‖∫ z in B ∩ D, F z‖ ≤ ε' * volume.real (B ∩ D) :=
    norm_setIntegral_le_of_norm_le_const
      ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top) fun z hz ↦ by
        rw [Real.norm_eq_abs]
        exact abs_extendedHeight_le_of_mem hσ hε'τ hh hz.2
  have h2 : ‖∫ z in B \ D, F z‖ ≤ τ * volume.real (B \ D) :=
    norm_setIntegral_le_of_norm_le_const
      ((measure_mono Set.sdiff_subset).trans_lt measure_ball_lt_top) fun z _ ↦ by
        rw [Real.norm_eq_abs, abs_le]
        exact LevelGraphFamily.extendedHeight_mem_Icc hτ D L s₁ s₂ h σ z
  have h3 : volume.real (B ∩ D) ≤ volume.real B :=
    measureReal_mono inter_subset_left measure_ball_lt_top.ne
  have h4 : |∫ z in B, F z| ≤ ε' * volume.real B + τ * volume.real (B \ D) := by
    rw [hsplit, ← Real.norm_eq_abs]
    calc ‖(∫ z in B ∩ D, F z) + ∫ z in B \ D, F z‖
        ≤ ‖∫ z in B ∩ D, F z‖ + ‖∫ z in B \ D, F z‖ := norm_add_le _ _
      _ ≤ ε' * volume.real (B ∩ D) + τ * volume.real (B \ D) := add_le_add h1 h2
      _ ≤ ε' * volume.real B + τ * volume.real (B \ D) := by
          have := mul_le_mul_of_nonneg_left h3 hε'
          linarith
  rw [setAverage_eq, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hBpos]
  calc (volume.real B)⁻¹ * |∫ z in B, F z|
      ≤ (volume.real B)⁻¹ * (ε' * volume.real B + τ * volume.real (B \ D)) :=
        mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hBpos.le)
    _ = ε' + τ * volume.real (B \ D) / volume.real B := by
        field_simp

/-! ### (B1) -/

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **(B1) The centers of an aligned height limit tend to zero.** Under the sharp energy bound, for
parameters with `0 < ℓ`, `0 ≤ b < 1`, `0 < ρ`, `0 < τ`, `0 < s₁`, `s₂ < 1` and `ρ + |r₀| < 2`,
the centers `a_j` of height-limit data along an aligned sequence tend to `0`. -/
theorem RigidityHypotheses.tendsto_alignedCenter_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * r ^ m)
    {ℓ r₀ b ρ τ s₁ s₂ c K : ℝ} {L : ℝ≥0}
    (hℓ : 0 < ℓ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hρ : 0 < ρ) (hτ : 0 < τ) (hs₁ : 0 < s₁)
    (hs₂ : s₂ < 1) (hρr₀ : ρ + |r₀| < 2)
    {x : ℕ → Space (m + 1)} {R : ℕ → ℝ} {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    {δ : ℕ → ℝ} {e : Space (m + 1)} (hal : IsAlignedSequence g u x R Q δ e)
    {φ : ℕ → ℕ} {σl a : ℕ → ℝ} {H : Space m → ℝ}
    (hlim : IsAlignedHeightLimit g u ℓ r₀ b ρ τ s₁ s₂ L c K x R Q δ φ σl a H) :
    Tendsto a atTop (𝓝 0) := by
  obtain ⟨-, hR, hRt, -, hδ0, -, htilt, he, hloc, hQ⟩ := hal
  obtain ⟨hφ, hσ, ha, -⟩ := hlim
  set v : ℕ → Space (m + 1) → ℝ := fun k z ↦ zeroExtension g u (x k + R k • Q k z) with hvdef
  have hV : VerticalPlanarLayers v :=
    hr.verticalPlanarLayers_of_rotated h hsharp x hR hRt he hloc hQ
  have hvL : ∀ k, LipschitzWith (⟨κ, h.kappa_pos.le⟩ * Real.toNNReal (R k)) (v k) := fun k ↦
    hr.lipschitzWith_rescaled h (x k) (hR k).le (Q k)
  have hvert : ‖verticalDirection m‖ = 1 := norm_verticalDirection m
  -- the bad volume tends to zero (HA1.2 with the cylinder normalization)
  set η : ℝ := (2 - ρ - |r₀|) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  set C : ℝ≥0∞ := ENNReal.ofReal ((5 : ℝ) ^ m) * volume (ball (0 : Space m) 1) /
    ENNReal.ofReal ℓ with hCdef
  have hC : C ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
      (ENNReal.ofReal_pos.mpr hℓ).ne'
  have hup : Tendsto (fun k ↦ C * ENNReal.ofReal (2 ^ m * δ k ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k ↦ (2 : ℝ) ^ m * δ k ^ 2) atTop (𝓝 0) := by
      have := (hδ0.pow 2).const_mul ((2 : ℝ) ^ m)
      rwa [zero_pow two_ne_zero, mul_zero] at this
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr hC)
    rwa [mul_zero] at h3
  have hbadT : Tendsto (fun k ↦ volume (closedBall (0 : Space m) ρ \
      goodProjection (R k) (v k) (verticalDirection m) ℓ r₀ b)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [hV.eventually_volume_sdiff_goodProjection_le hR
      (fun k ↦ (hvL k).locallyLipschitz) hvert hℓ r₀ hb0 hb1 ρ hη] with k hk
    refine hk.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) C)
    rw [← htilt k]
    exact setIntegral_closedBall_diffuseTiltDensity_le_cylinderTilt (hR k)
      (hvL k).locallyLipschitz (by rw [abs_of_pos hρ, hηdef]; linarith)
  -- the estimate of the centers
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := min (ε / 3) τ with hε'def
  have hε'pos : 0 < ε' := lt_min (by linarith) hτ
  have hε'τ : ε' ≤ τ := min_le_right _ _
  have hε'ε : ε' ≤ ε / 3 := min_le_left _ _
  have hBpos : 0 < volume.real (ball (0 : Space m) ρ) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ hρ).ne' measure_ball_lt_top.ne
  have hη₀ : 0 < ε / 3 * volume.real (ball (0 : Space m) ρ) / τ := by positivity
  have hlev := hV.levels (ρ + τ) ε' s₁ s₂ hε'pos hs₁ hs₂
  have hbad := hbadT.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη₀))
  filter_upwards [hφ.tendsto_atTop.eventually (hlev.and hbad)] with j hj
  obtain ⟨hj1, hj2⟩ := hj
  have hDm : MeasurableSet (verticalGoodSet (R (φ j)) (v (φ j)) ℓ r₀ b ρ) :=
    ((isOpen_goodProjection (hR (φ j)) (hvL (φ j)) hvert ℓ r₀ b).inter isOpen_ball).measurableSet
  have hsub : ball (0 : Space m) ρ \ verticalGoodSet (R (φ j)) (v (φ j)) ℓ r₀ b ρ ⊆
      closedBall (0 : Space m) ρ \
        goodProjection (R (φ j)) (v (φ j)) (verticalDirection m) ℓ r₀ b := by
    rintro y ⟨hyB, hyD⟩
    exact ⟨ball_subset_closedBall hyB, fun hyG ↦ hyD ⟨hyG, hyB⟩⟩
  have hvolD : volume.real (ball (0 : Space m) ρ \ verticalGoodSet (R (φ j)) (v (φ j)) ℓ r₀ b ρ) <
      ε / 3 * volume.real (ball (0 : Space m) ρ) / τ :=
    ENNReal.toReal_lt_of_lt_ofReal ((measure_mono hsub).trans_lt hj2)
  have hav := abs_setAverage_extendedHeight_le_of_bound (L := L)
    (h := fun s y ↦ slabLevelHeight (v (φ j)) τ s y) hDm hρ hτ.le (hσ j) hε'pos.le hε'τ
    (fun z hz ↦ (abs_slabLevelHeight_lt hε'pos hj1 (hσ j) hz.2).le)
  have hfrac : τ * volume.real (ball (0 : Space m) ρ \
      verticalGoodSet (R (φ j)) (v (φ j)) ℓ r₀ b ρ) / volume.real (ball (0 : Space m) ρ) <
      ε / 3 := by
    rw [div_lt_iff₀ hBpos]
    calc τ * volume.real (ball (0 : Space m) ρ \ verticalGoodSet (R (φ j)) (v (φ j)) ℓ r₀ b ρ)
        < τ * (ε / 3 * volume.real (ball (0 : Space m) ρ) / τ) :=
          mul_lt_mul_of_pos_left hvolD hτ
      _ = ε / 3 * volume.real (ball (0 : Space m) ρ) := by
          field_simp
  rw [Real.dist_eq, sub_zero, ha j]
  calc _ ≤ _ := hav
    _ < ε := by linarith

end SerrinEpigraph
