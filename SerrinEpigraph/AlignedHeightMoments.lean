module

public import SerrinEpigraph.AlignedHeightDecomposition
public import SerrinEpigraph.LowLevelProfileApproximation
public import SerrinEpigraph.HarmonicProjectedBadSet
public import SerrinEpigraph.HarmonicBadSetEnergy
public import SerrinEpigraph.AlignedCenterLimit

/-!
# Weighted height moments of aligned sequences (HA6.1)

This file proves the second conjunct (B2) of `HasAlignedHeightMoments` (blueprint
`harmonic-approximation.md`, HA6.1): along an aligned HA11 sequence with height-limit data
`IsAlignedHeightLimit`, the weighted height approximation
`∫_{Q_{1/2}} ((t - a_j)/δ_j - H(y))² ε |∇v_j|² → 0`.

The argument tests the HA5 total bound (`exists_stable_well_height_bounds_of_sharp_energy`) with
the `C¹` weight `w = ((t - a)/δ - H'(y)) η`, where `η` is a cutoff equal to `1` on `Q_{1/2}` and
`H'` a compactly supported `C¹` function equal to `H` a.e. on `B_{5/8}`. This reduces the stable
well to the transition region `0 < v < s₂` (with `1 - s₂` below the HA5 threshold), which is
split into
* tilt-bad points: HA1.1 (`lintegral_weighted_bad_set_le`) with the thin layer (HA8), weight
  `O((δ'' + |a|)²/δ²)` against bad mass `O(δ²)`;
* good points with levels in `[s₁, s₂]`: the level graph family of the height data, where the
  change of variables (`LevelGraphFamily.lintegral_levelRegion_eq`) has a bounded weight and HA3
  makes all levels share the limit `H`;
* good points with levels below `s₁`: HA10 (`exists_low_profile_approximation_of_le`, the band
  localization and the density bound) with vertical Fubini (`setIntegral_le_of_vertical_band`).

The regular representative `H'` is where the flux identification (C) enters: `H` is only an `L²`
limit, and bad-set gradient mass may concentrate on the columns where an `L²` function is large,
so the weighted approximation needs `H` bounded near `B_{1/2}`. Under (C) the limit is weakly
harmonic, hence smooth (`RigidityHypotheses.exists_regular_alignedHeightLimit`).

* `RigidityHypotheses.exists_low_profile_approximation_of_le`: HA10.a–b with an arbitrary
  smaller anchor threshold `ℓ₁ ≤ ℓ` (the good set of the height data may use any threshold).
* `transitionHeightMoment_le`, `RigidityHypotheses.heightMoment_le_of_scale`: the estimate at
  a single scale.
* `RigidityHypotheses.tendsto_alignedHeightMoment_of_regular`: (B2) given `a_j → 0` and a
  regular representative of `H`.
* `RigidityHypotheses.tendsto_alignedHeightMoment`: (B2) from the flux identification (C).
* `RigidityHypotheses.hasAlignedHeightMoments_of_fluxIdentification`: (B) from (C), with (B1)
  from `RigidityHypotheses.tendsto_alignedCenter_zero`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal ENNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

private theorem norm_point_sub_point_ahm (y : Space m) (t t' : ℝ) :
    ‖point y t - point y t'‖ = |t - t'| := by
  have h := point_add_vertical y t' (t - t')
  rw [show t' + (t - t') = t by ring] at h
  rw [← h, add_sub_cancel_left, norm_smul, norm_verticalDirection, mul_one, Real.norm_eq_abs]

private theorem abs_last_sub_le_norm_ahm (z w : Space (m + 1)) :
    |z (Fin.last m) - w (Fin.last m)| ≤ ‖z - w‖ := by
  have h := abs_real_inner_le_norm (EuclideanSpace.single (Fin.last m) (1 : ℝ)) (z - w)
  simpa [EuclideanSpace.inner_single_left] using h

/-! ### HA10 with an arbitrary smaller anchor threshold -/

/-- **HA10.a + HA10.b with a smaller anchor threshold.** As
`RigidityHypotheses.exists_low_profile_approximation`, but the horizontal set `D` only has to
contain the lines carrying good points at an arbitrary threshold `ℓ₁ ≤ ℓ`; the degraded bad
threshold `ℓ'` then depends on `ℓ₁`. -/
theorem RigidityHypotheses.exists_low_profile_approximation_of_le (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m) :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ (K α : ℝ), 0 < K → 0 < α → ∀ b₀ ∈ Ioo (0 : ℝ) 1,
      ∀ s ∈ Ioo (0 : ℝ) α₁, s < 1 - b₀ → ∀ Lc : ℝ≥0,
      ∃ ℓ ρ₀ Cw : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ 0 < Cw ∧
      ∀ ℓ₁ : ℝ, 0 < ℓ₁ → ℓ₁ ≤ ℓ → ∃ ℓ' : ℝ, 0 < ℓ' ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
      ∀ (D : Set (Space m)) (r₀ τs η β ρD b : ℝ),
        ρ₀ ≤ R * r₀ → Cw ≤ R * r₀ → 0 < η → η + Cw / R < τs → β ≤ b₀ → s < 1 - β → b ≤ s →
        HasLevelCone (fun z ↦ zeroExtension g u (x + R • Q z)) D τs s s Lc →
        (∀ A, IsLayerGoodPoint R (fun z ↦ zeroExtension g u (x + R • Q z))
          (verticalDirection m) ℓ₁ r₀ b₀ A → |A (Fin.last m)| < τs → ‖horizontal A‖ < ρD →
            horizontal A ∈ D) →
        (∀ y ∈ D, ∀ t ∈ Ioo (-τs) τs, t ≤ -η →
          zeroExtension g u (x + R • Q (point y t)) = 0) →
        (∀ y ∈ D, ∀ t ∈ Ioo (-τs) τs, η ≤ t →
          1 - β < zeroExtension g u (x + R • Q (point y t))) →
        ∀ y ∈ D, ‖y‖ + Cw / R < ρD → ∀ t ∈ Ioo (-τs) τs,
          0 < zeroExtension g u (x + R • Q (point y t)) →
          zeroExtension g u (x + R • Q (point y t)) < b →
          (∃ r ∈ Ioc 0 (2 * r₀), ℓ' * r ^ m ≤ ∫ z in ball (point y t) r,
            diffuseTiltDensity R (fun z ↦ zeroExtension g u (x + R • Q z))
              (verticalDirection m) z) ∨
          ∀ z ∈ ball (point y t) (K * α / R),
            |zeroExtension g u (x + R • Q z) - layerProfile f (R * (z (Fin.last m) -
              (slabLevelHeight (fun z ↦ zeroExtension g u (x + R • Q z)) τs s y -
                layerTravelTime f s / R)))| ≤ α := by
  obtain ⟨a₀, α₁, ha₀, hα₁, hnd⟩ := hr.exists_microscopic_nondegeneracy h
  refine ⟨α₁, hα₁, ?_⟩
  intro K α hK hα b₀ hb₀ s hs hsb Lc
  have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, by linarith [hb₀.1]⟩
  set T1 := layerTravelTime f (1 - b₀) with hT1
  set Ts := layerTravelTime f s with hTs
  have hT1 : 0 ≤ T1 := hr.layerTravelTime_nonneg h ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩
  have hTs0 : 0 < Ts := hr.layerTravelTime_pos h hs01
  set Cn := s / a₀ with hCn
  have hCn0 : 0 < Cn := div_pos hs.1 ha₀
  set K' := K * α + (1 + (Lc : ℝ)) * Cn + T1 + Ts + 1 with hK'
  have hK'0 : 0 ≤ K' := by positivity
  obtain ⟨ℓ, ρ₀, hℓ, hρ₀, hdich⟩ := hr.exists_microscopic_profile_dichotomy h hbound
    (α := α) (K' := K') hα hK'0 hb₀ hs01
  set Wd := K' + T1 + Ts + 3 with hWd
  set Cw := Wd + Cn + 1 with hCw
  have hm1 : Module.finrank ℝ (Space (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  set vol₁ := volume.real (ball (0 : Space (m + 1)) 1) with hvol₁
  have hvol₁pos : 0 < vol₁ := by
    rw [hvol₁, Measure.real]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne'
      (measure_ball_lt_top (μ := volume)).ne
  have hκ := h.kappa_pos
  refine ⟨ℓ, ρ₀, Cw, hℓ, hρ₀, by positivity, ?_⟩
  intro ℓ₁ hℓ₁ hℓ₁ℓ
  set cℓ := ℓ₁ / (κ ^ 2 * vol₁) with hcℓ
  have hcℓ0 : 0 < cℓ := by positivity
  set ℓ' := ℓ₁ * min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) with hℓ'
  have hℓ'0 : 0 < ℓ' := mul_pos hℓ₁ (lt_min (by positivity) (by positivity))
  refine ⟨ℓ', hℓ'0, ?_⟩
  intro x R hR Q D r₀ τs η β ρD b hρR hCwR hη hητ hβ hsβ hbs hcone hfull hlow hhigh
    y hy hyρ t ht hpos hlowb
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • Q z) with hvdef
  have hvc : Continuous v :=
    h.zeroExtension_continuous.comp (continuous_const.add (Q.continuous.const_smul R))
  have hCwR' : Cw / R ≤ r₀ := by rw [div_le_iff₀ hR]; linarith
  have hητ' : η < τs := by
    have : 0 < Cw / R := by positivity
    linarith
  have hlowb' : v (point y t) < b := hlowb
  -- the low point lies in the slab
  have htη : t ∈ Ioo (-η) η := by
    constructor
    · by_contra hn
      have := hlow y hy t ht (not_lt.mp hn)
      linarith
    · by_contra hn
      have := hhigh y hy t ht (not_lt.mp hn)
      linarith
  -- either `p` is bad at the threshold `ℓ'`, or it is a good anchor at the threshold `ℓ ≥ ℓ'`
  by_cases hbad : ∃ r ∈ Ioc 0 (2 * r₀), ℓ' * r ^ m ≤ ∫ z in ball (point y t) r,
      diffuseTiltDensity R v (verticalDirection m) z
  · exact Or.inl hbad
  push Not at hbad
  have hℓ'ℓ : ℓ' ≤ ℓ := by
    have h1 : min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) ≤ 1 :=
      (min_le_left _ _).trans (pow_le_one₀ (by norm_num) (by norm_num))
    calc ℓ' = ℓ₁ * min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) := hℓ'
      _ ≤ ℓ₁ * 1 := mul_le_mul_of_nonneg_left h1 hℓ₁.le
      _ = ℓ₁ := mul_one ℓ₁
      _ ≤ ℓ := hℓ₁ℓ
  have hpos' : 0 < v (point y t) := hpos
  obtain ⟨tA, htA, hA⟩ : ∃ tA, |tA| < τs ∧
      IsLayerGoodPoint R v (verticalDirection m) ℓ r₀ b₀ (point y tA) := by
    refine ⟨t, abs_lt.mpr ht, ⟨hpos', by linarith⟩, fun r hr ↦ ?_⟩
    exact (hbad r ⟨hr.1, by linarith [hr.1, hr.2]⟩).trans_le
      (mul_le_mul_of_nonneg_right hℓ'ℓ (pow_nonneg hr.1.le m))
  set A := point y tA with hAdef
  set e := Q (verticalDirection m) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, LinearIsometryEquiv.norm_map]; exact norm_verticalDirection m
  set X := x + R • Q A with hXdef
  have hline : ∀ τ : ℝ, zeroExtension g u (X + τ • e) = v (point y (tA + τ / R)) := by
    intro τ
    simp only [hvdef, hXdef, hAdef, hedef]
    rw [← point_add_vertical, map_add, map_smul, smul_add, smul_smul, mul_div_cancel₀ _ hR.ne',
      add_assoc]
  have hpt : ∀ z : Space (m + 1), zeroExtension g u (X + R • Q (z - A)) = v z := by
    intro z
    simp only [hvdef, hXdef]
    rw [map_sub, smul_sub, add_add_sub_cancel]
  have hinner : ∀ z : Space (m + 1), inner ℝ e (R • Q (z - A)) = R * (z (Fin.last m) - tA) := by
    intro z
    rw [hedef, real_inner_smul_right, LinearIsometryEquiv.inner_map_map, real_inner_comm,
      inner_verticalDirection_right, hAdef]
    simp [last_point]
  have hUX : zeroExtension g u X ∈ Ioo 0 (1 - b₀) := hA.1
  have htilt : ∀ ρ ∈ Ioc 0 ρ₀, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
      ℓ * ρ ^ m := fun ρ hρ ↦
    physical_tilt_lt_of_isLayerGoodPoint_rotated hR Q hA hρ.1 (hρ.2.trans hρR)
  have htAη : tA ∈ Ioo (-η) η := by
    have hvA : v A ∈ Ioo 0 (1 - b₀) := hA.1
    have htA' : tA ∈ Ioo (-τs) τs := abs_lt.mp htA
    constructor
    · by_contra hn
      have := hlow y hy tA htA' (not_lt.mp hn)
      rw [← hAdef] at this
      linarith [hvA.1]
    · by_contra hn
      have := hhigh y hy tA htA' (not_lt.mp hn)
      rw [← hAdef] at this
      linarith [hvA.2]
  have hwin : ∀ τ : ℝ, |τ| ≤ Wd → tA + τ / R ∈ Ioo (-τs) τs := by
    intro τ hτ
    have h1 : |τ / R| ≤ Wd / R := by
      rw [abs_div, abs_of_pos hR]
      exact div_le_div_of_nonneg_right hτ hR.le
    have h2 : Wd / R ≤ Cw / R := div_le_div_of_nonneg_right (by linarith) hR.le
    rw [abs_le] at h1
    constructor <;> linarith [htAη.1, htAη.2]
  rcases hdich X e he hUX htilt with hdown | ⟨⟨τc, hτc, hτcs⟩, happrox⟩
  · -- a downward crossing contradicts the cone condition
    exfalso
    obtain ⟨τ₁, τ₂, h1, h2, h3, h4, h5⟩ := hdown
    have hτ₁ : |τ₁| ≤ Wd := abs_le.mpr ⟨by linarith, by linarith⟩
    have hτ₂ : |τ₂| ≤ Wd := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [hline] at h4 h5
    exact no_downward_crossing_of_cone hvc hcone hη hητ' hs.1 hlow hy
      (hwin τ₁ hτ₁) (hwin τ₂ hτ₂) (by
        have : τ₁ / R < τ₂ / R := div_lt_div_of_pos_right h2 hR
        linarith) h4 h5
  · -- the crossing is the slab level height
    have hτcW : |τc| ≤ Wd := abs_le.mpr ⟨by linarith [hτc.1], by linarith [hτc.2]⟩
    have hcross : ∃ t' ∈ Ioo (-τs) τs, v (point y t') = s :=
      ⟨tA + τc / R, hwin τc hτcW, by rw [← hline]; exact hτcs⟩
    obtain ⟨hHmem, hHval⟩ := slabLevelHeight_spec hcross
    set ts := slabLevelHeight v τs s y with htsdef
    have htseq : ts = tA + τc / R := by
      have hh := hcone s ⟨le_rfl, le_rfl⟩ y hy y hy ts hHmem (tA + τc / R) (hwin τc hτcW)
        hHval (by rw [← hline]; exact hτcs)
      rw [dist_self, mul_zero] at hh
      have := abs_nonpos_iff.mp hh
      linarith
    have hτceq : τc = R * (ts - tA) := by rw [htseq]; field_simp; ring
    -- the CO3 point near `p`
    set p := point y t with hpdef
    obtain ⟨z₀, hz₀, hz₀s⟩ := hnd x R hR Q p s hs.1 hs.2.le hpos
    have hseg : ContinuousOn (fun lam : ℝ ↦ v (p + lam • (z₀ - p))) (Icc 0 1) :=
      (hvc.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    obtain ⟨lam, hlam, hlams⟩ := intermediate_value_Icc zero_le_one hseg
      (show s ∈ Icc (v (p + (0 : ℝ) • (z₀ - p))) (v (p + (1 : ℝ) • (z₀ - p))) by
        rw [zero_smul, add_zero, one_smul, add_sub_cancel]
        exact ⟨(hlowb'.trans_le hbs).le, hz₀s.le⟩)
    set p' := p + lam • (z₀ - p) with hp'def
    have hpp' : ‖p' - p‖ < Cn / R := by
      have h1 : ‖p' - p‖ = lam * ‖z₀ - p‖ := by
        rw [hp'def, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.1]
      have h2 : ‖z₀ - p‖ < s / (a₀ * R) := by rwa [mem_ball, dist_eq_norm] at hz₀
      have h3 : s / (a₀ * R) = Cn / R := by rw [hCn]; field_simp
      rw [h1, ← h3]
      calc lam * ‖z₀ - p‖ ≤ 1 * ‖z₀ - p‖ := mul_le_mul_of_nonneg_right hlam.2 (norm_nonneg _)
        _ < s / (a₀ * R) := by rw [one_mul]; exact h2
    set y' := horizontal p' with hy'def
    set t' := p' (Fin.last m) with ht'def
    have hp'pt : point y' t' = p' := point_horizontal_last p'
    have hvp' : v (point y' t') = s := by rw [hp'pt]; exact hlams
    have htt' : |t' - t| < Cn / R := by
      have := abs_last_sub_le_norm_ahm p' p
      rw [hpdef, last_point] at this
      exact this.trans_lt hpp'
    have hCnCw : Cn / R ≤ Cw / R := div_le_div_of_nonneg_right (by linarith) hR.le
    have ht'm : t' ∈ Ioo (-τs) τs := by
      rw [abs_lt] at htt'
      constructor <;> linarith [htη.1, htη.2]
    have hyy' : dist y' y < Cn / R := by
      have := lipschitzWith_one_horizontal.dist_le_mul p' p
      rw [NNReal.coe_one, one_mul, hpdef, horizontal_point, dist_eq_norm] at this
      rw [hy'def]
      exact this.trans_lt hpp'
    have hy'ρ : ‖y'‖ < ρD := by
      have := norm_le_norm_add_norm_sub' y' y
      rw [← dist_eq_norm] at this
      linarith
    by_cases hy'D : y' ∈ D
    · -- the window: `|t - ts| ≤ (1 + Lc) Cn / R`
      right
      have hh := hcone s ⟨le_rfl, le_rfl⟩ y' hy'D y hy t' ht'm ts hHmem hvp' hHval
      have hwin' : |t - ts| < (1 + (Lc : ℝ)) * Cn / R := by
        have h1 : |t' - ts| ≤ (Lc : ℝ) * (Cn / R) :=
          hh.trans (mul_le_mul_of_nonneg_left hyy'.le Lc.coe_nonneg)
        calc |t - ts| ≤ |t - t'| + |t' - ts| := abs_sub_le _ _ _
          _ < Cn / R + (Lc : ℝ) * (Cn / R) := by rw [abs_sub_comm]; linarith
          _ = (1 + (Lc : ℝ)) * Cn / R := by ring
      intro z hz
      have hZ : R • Q (z - A) ∈ closedBall (0 : Space (m + 1)) K' := by
        rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hR.le,
          LinearIsometryEquiv.norm_map]
        have hzA : ‖z - A‖ ≤ ‖z - p‖ + |t - ts| + |ts - tA| := by
          have h1 : z - A = (z - p) + (point y t - point y ts) + (point y ts - A) := by
            rw [hpdef]; abel
          rw [h1]
          calc ‖(z - p) + (point y t - point y ts) + (point y ts - A)‖
              ≤ ‖z - p‖ + ‖point y t - point y ts‖ + ‖point y ts - A‖ := norm_add₃_le
            _ = _ := by rw [norm_point_sub_point_ahm, hAdef, norm_point_sub_point_ahm]
        have hzp : ‖z - p‖ < K * α / R := by rwa [mem_ball, dist_eq_norm] at hz
        have hts : |ts - tA| = |τc| / R := by
          rw [htseq, show tA + τc / R - tA = τc / R by ring, abs_div, abs_of_pos hR]
        have hτcb : |τc| ≤ T1 + Ts + 1 := abs_le.mpr ⟨by linarith [hτc.1], by linarith [hτc.2]⟩
        have hRzp : R * ‖z - p‖ < K * α := by
          have := (lt_div_iff₀ hR).mp hzp
          linarith [mul_comm R ‖z - p‖]
        have hRtts : R * |t - ts| < (1 + (Lc : ℝ)) * Cn := by
          have := (lt_div_iff₀ hR).mp hwin'
          linarith [mul_comm R |t - ts|]
        have hRtsA : R * |ts - tA| = |τc| := by
          rw [hts]
          field_simp
        have key : R * ‖z - A‖ ≤ K * α + (1 + (Lc : ℝ)) * Cn + (T1 + Ts + 1) := by
          have h1 : R * ‖z - A‖ ≤ R * ‖z - p‖ + R * |t - ts| + R * |ts - tA| := by
            have := mul_le_mul_of_nonneg_left hzA hR.le
            linarith
          linarith
        rw [hK']
        linarith
      have happ := happrox (R * (ts - tA)) (by rw [← hτceq]; exact hτc)
        (by rw [← hτceq]; exact hτcs) _ hZ
      rw [hpt, hinner] at happ
      have harg : R * (z (Fin.last m) - tA) - R * (ts - tA) + Ts =
          R * (z (Fin.last m) - (ts - Ts / R)) := by field_simp; ring
      rw [harg] at happ
      exact happ
    · -- the CO3 point is bad, and so is `p` at the degraded threshold
      left
      have hp'good : ¬IsLayerGoodPoint R v (verticalDirection m) ℓ₁ r₀ b₀ p' := by
        intro hg
        apply hy'D
        have := hfull p' hg (by rw [← ht'def]; exact abs_lt.mpr ⟨ht'm.1, ht'm.2⟩)
          (by rw [← hy'def]; exact hy'ρ)
        rwa [← hy'def] at this
      have hval' : v p' ∈ Ioo 0 (1 - b₀) := by
        rw [show v p' = s from hlams]
        exact ⟨hs.1, hsb⟩
      have hbadr : ∃ r ∈ Ioc 0 r₀, ℓ₁ * r ^ m ≤
          ∫ z in ball p' r, diffuseTiltDensity R v (verticalDirection m) z := by
        by_contra hn
        push Not at hn
        exact hp'good ⟨hval', hn⟩
      obtain ⟨r, hr0, hrbad⟩ := hbadr
      -- microscopic radii cannot be bad
      have hLipv : LipschitzWith ⟨κ * R, by positivity⟩ v := by
        apply LipschitzWith.of_dist_le_mul
        intro a c
        have := (hr.zeroExtension_lipschitzWith h).dist_le_mul (x + R • Q a) (x + R • Q c)
        rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hR.le, Q.dist_map] at this
        calc dist (v a) (v c) ≤ κ * (R * dist a c) := this
          _ = κ * R * dist a c := by ring
      have hRr : cℓ ≤ R * r := by
        have hint := integrableOn_diffuseTiltDensity hLipv.locallyLipschitz
          (isCompact_closedBall p' r) R (norm_verticalDirection m)
        have hle : ∫ z in ball p' r, diffuseTiltDensity R v (verticalDirection m) z ≤
            (κ * R) ^ 2 / R * volume.real (ball p' r) := by
          have hconst : IntegrableOn (fun _ : Space (m + 1) ↦ (κ * R) ^ 2 / R) (ball p' r) :=
            integrableOn_const (measure_ball_lt_top (μ := volume)).ne
          have := setIntegral_mono (hint.mono_set ball_subset_closedBall) hconst
            (fun z ↦ diffuseTiltDensity_le_of_lipschitzWith hR hLipv (verticalDirection m) z)
          rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
        have hvolr : volume.real (ball p' r) = r ^ (m + 1) * vol₁ := by
          rw [Measure.real, Measure.addHaar_ball volume p' hr0.1.le, hm1, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (pow_nonneg hr0.1.le _), hvol₁, Measure.real]
        rw [hvolr] at hle
        have h1 : ℓ₁ * r ^ m ≤ (κ * R) ^ 2 / R * (r ^ (m + 1) * vol₁) := hrbad.trans hle
        have h2 : (κ * R) ^ 2 / R * (r ^ (m + 1) * vol₁) = (κ ^ 2 * vol₁ * (R * r)) * r ^ m := by
          field_simp
          ring
        rw [h2] at h1
        have h3 : ℓ₁ ≤ κ ^ 2 * vol₁ * (R * r) := le_of_mul_le_mul_right h1 (pow_pos hr0.1 m)
        rw [hcℓ, div_le_iff₀ (by positivity)]
        linarith
      rcases le_or_gt (Cn / R) r with hrbig | hrsmall
      · refine ⟨2 * r, ⟨by linarith [hr0.1], by linarith [hr0.2]⟩, ?_⟩
        have hsub : ball p' r ⊆ ball p (2 * r) := by
          intro z hz
          rw [mem_ball] at hz ⊢
          have := dist_triangle z p' p
          rw [dist_eq_norm p' p] at this
          linarith
        have hint := integrableOn_diffuseTiltDensity hLipv.locallyLipschitz
          (isCompact_closedBall p (2 * r)) R (norm_verticalDirection m)
        have hmono : ∫ z in ball p' r, diffuseTiltDensity R v (verticalDirection m) z ≤
            ∫ z in ball p (2 * r), diffuseTiltDensity R v (verticalDirection m) z :=
          setIntegral_mono_set (hint.mono_set ball_subset_closedBall)
            (Eventually.of_forall fun z ↦ diffuseTiltDensity_nonneg hR _
              (norm_verticalDirection m) z) (Eventually.of_forall hsub)
        have hmin2 : min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) * 2 ^ m ≤ 1 := by
          calc min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) * 2 ^ m
              ≤ (1 / 2 : ℝ) ^ m * 2 ^ m :=
                mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
            _ = 1 := by rw [← mul_pow]; norm_num
        have hrm : 0 ≤ r ^ m := pow_nonneg hr0.1.le m
        have hℓ'le : ℓ' * (2 * r) ^ m ≤ ℓ₁ * r ^ m := by
          calc ℓ' * (2 * r) ^ m
              = ℓ₁ * (min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) * 2 ^ m) * r ^ m := by
                rw [hℓ', mul_pow]
                ring
            _ ≤ ℓ₁ * 1 * r ^ m :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin2 hℓ₁.le) hrm
            _ = ℓ₁ * r ^ m := by ring
        linarith
      · refine ⟨2 * Cn / R, ⟨by positivity, by
          have : Cn / R ≤ r₀ := hCnCw.trans hCwR'
          rw [mul_div_assoc]; linarith⟩, ?_⟩
        have hsub : ball p' r ⊆ ball p (2 * Cn / R) := by
          intro z hz
          rw [mem_ball] at hz ⊢
          have := dist_triangle z p' p
          rw [dist_eq_norm p' p] at this
          have : 2 * Cn / R = Cn / R + Cn / R := by ring
          linarith
        have hint := integrableOn_diffuseTiltDensity hLipv.locallyLipschitz
          (isCompact_closedBall p (2 * Cn / R)) R (norm_verticalDirection m)
        have hmono : ∫ z in ball p' r, diffuseTiltDensity R v (verticalDirection m) z ≤
            ∫ z in ball p (2 * Cn / R), diffuseTiltDensity R v (verticalDirection m) z :=
          setIntegral_mono_set (hint.mono_set ball_subset_closedBall)
            (Eventually.of_forall fun z ↦ diffuseTiltDensity_nonneg hR _
              (norm_verticalDirection m) z) (Eventually.of_forall hsub)
        have hrlow : cℓ / R ≤ r := by rw [div_le_iff₀ hR]; linarith
        have hℓ'le : ℓ' * (2 * Cn / R) ^ m ≤ ℓ₁ * r ^ m := by
          have h1 : ℓ' ≤ ℓ₁ * (cℓ / (2 * Cn)) ^ m := by
            rw [hℓ']
            exact mul_le_mul_of_nonneg_left (min_le_right _ _) hℓ₁.le
          have h2 : (cℓ / (2 * Cn)) ^ m * (2 * Cn / R) ^ m = (cℓ / R) ^ m := by
            rw [← mul_pow]
            congr 1
            field_simp
          have h3 : (cℓ / R) ^ m ≤ r ^ m := pow_le_pow_left₀ (by positivity) hrlow m
          calc ℓ' * (2 * Cn / R) ^ m ≤ ℓ₁ * (cℓ / (2 * Cn)) ^ m * (2 * Cn / R) ^ m :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = ℓ₁ * (cℓ / R) ^ m := by rw [mul_assoc, h2]
            _ ≤ ℓ₁ * r ^ m := mul_le_mul_of_nonneg_left h3 hℓ₁.le
        linarith

/-! ### Auxiliary facts -/

/-- A level graph family restricts to subsets of its horizontal set. -/
theorem LevelGraphFamily.of_subset {v : Space (m + 1) → ℝ} {D D' : Set (Space m)}
    {τ s₁ s₂ T c : ℝ} {L : ℝ≥0} {hh : ℝ → Space m → ℝ}
    (hG : LevelGraphFamily v D τ s₁ s₂ T c L hh) (hD : D' ⊆ D) :
    LevelGraphFamily v D' τ s₁ s₂ T c L hh where
  continuous := hG.continuous
  mem_slab s hs y hy := hG.mem_slab s hs y (hD hy)
  level s hs y hy := hG.level s hs y (hD hy)
  unique s hs y hy := hG.unique s hs y (hD hy)
  lipschitzOnWith s hs := (hG.lipschitzOnWith s hs).mono hD
  differentiableAt s hs y hy := hG.differentiableAt s hs y (hD hy)
  vertical_lower s hs y hy := hG.vertical_lower s hs y (hD hy)

/-- The rotated rescaled translates satisfy the kinetic growth bound at every center. -/
theorem RigidityHypotheses.rotated_kinetic_ball_le (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (x : Space (m + 1)) {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (p : Space (m + 1)) {r : ℝ} (hr0 : 0 < r) :
    (∫ y in ball p r, ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R) ≤
      (2 * L) * r ^ m := by
  set W : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • z) with hW
  have hpt : ∀ y, ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) y‖ ^ 2 / R =
      ‖gradient W (Q y)‖ ^ 2 / R := by
    intro y
    have hfun : (fun z ↦ zeroExtension g u (x + R • Q z)) = fun z ↦ W (Q z) := rfl
    rw [hfun, gradient_comp_linearIsometryEquiv, LinearIsometryEquiv.norm_map]
  simp_rw [hpt]
  have hh := (Q.measurePreserving.restrict_preimage (s := ball (Q p) r)
    measurableSet_ball).integral_comp Q.toHomeomorph.measurableEmbedding
    (fun z ↦ ‖gradient W z‖ ^ 2 / R)
  rw [Q.preimage_ball, LinearIsometryEquiv.symm_apply_apply] at hh
  rw [hh]
  exact hr.translated_kinetic_ball_le_surface_bound h hbound x hR (Q p) hr0

/-- **HA1.1 for the rotated rescaled translates.** The gradient mass of the tilt-bad points is
bounded by the tilt over a compact set containing their bad balls. -/
theorem RigidityHypotheses.rotated_kinetic_bad_set_le (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (x : Space (m + 1)) {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    {A : Set (Space (m + 1))} (hA : IsCompact A) (R' : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫⁻ p in {p | ∃ r : ℝ, 0 < r ∧ r ≤ R' ∧ ball p r ⊆ A ∧
        η * r ^ m ≤ ∫ y in ball p r, diffuseTiltDensity R
          (fun z ↦ zeroExtension g u (x + R • Q z)) (verticalDirection m) y},
      ENNReal.ofReal (‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R)) ≤
      (ENNReal.ofReal ((2 * L) * (5 : ℝ) ^ m) / ENNReal.ofReal η) *
        ENNReal.ofReal (∫ p in A, diffuseTiltDensity R
          (fun z ↦ zeroExtension g u (x + R • Q z)) (verticalDirection m) p) := by
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • Q z) with hvdef
  have hvL : LocallyLipschitz v := h.locallyLipschitz_rescaled_translate x R Q
  have hq : IntegrableOn (diffuseTiltDensity R v (verticalDirection m)) A :=
    integrableOn_diffuseTiltDensity hvL hA R (norm_verticalDirection m)
  have hw : LocallyIntegrable (fun p ↦ ‖gradient v p‖ ^ 2 / R) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact (integrableOn_gradient_sq_of_locallyLipschitz hvL hK).div_const R
  exact lintegral_weighted_bad_set_le hA.measurableSet hq
    (fun p ↦ diffuseTiltDensity_nonneg hR v (norm_verticalDirection m) p) hw
    (fun p ↦ by positivity) R' m (by positivity) hη
    (fun p r hr0 ↦ hr.rotated_kinetic_ball_le h hbound x hR Q p hr0)

/-- **The level-graph region in level coordinates.** Over a level graph family with
`|∇v| ≤ K T`, the weighted gradient mass `∫ (|∇v|² / T) w²` of the level region is bounded by
`K² / c (s₂ - s₁) ∫_D W` as soon as `w² ≤ W(y)` at the level points over `y`. -/
theorem LevelGraphFamily.lintegral_levelRegion_weighted_le {v : Space (m + 1) → ℝ}
    {D : Set (Space m)} {τ s₁ s₂ T c : ℝ} {L : ℝ≥0} {hh : ℝ → Space m → ℝ}
    (hG : LevelGraphFamily v D τ s₁ s₂ T c L hh) (hT : 0 < T) (hc : 0 < c) (hs : s₁ ≤ s₂)
    (hD : MeasurableSet D) {Kv : ℝ} (hgrad : ∀ z, ‖gradient v z‖ ≤ Kv * T)
    {w : Space (m + 1) → ℝ} (hw : Measurable w) {W : Space m → ℝ}
    (hW : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, w (point y (hh s y)) ^ 2 ≤ W y) :
    ∫⁻ z in levelRegion v D τ s₁ s₂, ENNReal.ofReal (‖gradient v z‖ ^ 2 / T * w z ^ 2) ≤
      ENNReal.ofReal (Kv ^ 2 / c * (s₂ - s₁)) * ∫⁻ y in D, ENNReal.ofReal (W y) := by
  have hΦ : Measurable (fun z ↦ ENNReal.ofReal (‖gradient v z‖ ^ 2 / T * w z ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      ((((measurable_gradient v).norm.pow_const 2).div_const T).mul (hw.pow_const 2))
  rw [hG.lintegral_levelRegion_eq hT hc hs hD hΦ]
  calc ∫⁻ y in D, ∫⁻ s in Icc s₁ s₂,
        ENNReal.ofReal (‖gradient v (point y (hh s y))‖ ^ 2 / T * w (point y (hh s y)) ^ 2) /
          ENNReal.ofReal (verticalDerivative v (point y (hh s y)))
      ≤ ∫⁻ y in D, ∫⁻ _ in Icc s₁ s₂, ENNReal.ofReal (Kv ^ 2 / c * W y) := by
        refine setLIntegral_mono' hD fun y hy ↦ setLIntegral_mono' measurableSet_Icc
          fun s hs' ↦ ?_
        have hdv : c * T ≤ verticalDerivative v (point y (hh s y)) :=
          hG.mul_le_verticalDerivative hT hs' hy
        have hdpos : 0 < verticalDerivative v (point y (hh s y)) :=
          lt_of_lt_of_le (mul_pos hc hT) hdv
        rw [← ENNReal.ofReal_div_of_pos hdpos]
        apply ENNReal.ofReal_le_ofReal
        have h1 : ‖gradient v (point y (hh s y))‖ ^ 2 ≤ (Kv * T) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hgrad _) 2
        have h2 := hW s hs' y hy
        have hW0 : 0 ≤ W y := (sq_nonneg _).trans h2
        rw [div_le_iff₀ hdpos]
        calc ‖gradient v (point y (hh s y))‖ ^ 2 / T * w (point y (hh s y)) ^ 2
            ≤ (Kv * T) ^ 2 / T * W y :=
              mul_le_mul (div_le_div_of_nonneg_right h1 hT.le) h2 (sq_nonneg _) (by positivity)
          _ = Kv ^ 2 / c * W y * (c * T) := by field_simp
          _ ≤ Kv ^ 2 / c * W y * verticalDerivative v (point y (hh s y)) :=
              mul_le_mul_of_nonneg_left hdv (by positivity)
    _ = ∫⁻ y in D, ENNReal.ofReal (Kv ^ 2 / c * (s₂ - s₁)) * ENNReal.ofReal (W y) := by
        refine setLIntegral_congr_fun hD fun y hy ↦ ?_
        rw [setLIntegral_const, Real.volume_Icc]
        by_cases hW0 : 0 ≤ W y
        · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
        · push Not at hW0
          rw [ENNReal.ofReal_of_nonpos (by
            have : 0 ≤ Kv ^ 2 / c := by positivity
            nlinarith), ENNReal.ofReal_of_nonpos hW0.le, zero_mul, mul_zero]
    _ = ENNReal.ofReal (Kv ^ 2 / c * (s₂ - s₁)) * ∫⁻ y in D, ENNReal.ofReal (W y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ### The height weight -/

/-- The cutoff of the height weight: `1` on `Q_{1/2}`, supported in `|y| < 9/16`, `|t| < 5/8`. -/
theorem exists_heightMomentCutoff :
    ∃ η : Space (m + 1) → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧ (∀ z, |η z| ≤ 1) ∧
      (∀ z ∈ tiltCylinder (verticalDirection m) (1 / 2), η z = 1) ∧
      (∀ z, η z ≠ 0 → ‖horizontal z‖ < 9 / 16 ∧ |z (Fin.last m)| < 5 / 8) ∧
      tsupport η ⊆ ball (0 : Space (m + 1)) (5 / 4) ∧
      (∀ z ∈ tsupport η, |z (Fin.last m)| ≤ 5 / 8) ∧
      ∃ Cη : ℝ, ∀ z, ‖fderiv ℝ η z‖ ≤ Cη := by
  let b₁ : ContDiffBump (0 : Space m) := ⟨1 / 2, 9 / 16, by norm_num, by norm_num⟩
  let b₂ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 5 / 8, by norm_num, by norm_num⟩
  set η : Space (m + 1) → ℝ := fun z ↦ b₁ (horizontal z) * b₂ (z (Fin.last m)) with hηdef
  have hlastc : Continuous (fun z : Space (m + 1) ↦ z (Fin.last m)) :=
    (EuclideanSpace.proj (Fin.last m) : Space (m + 1) →L[ℝ] ℝ).continuous
  have hlast : ContDiff ℝ 1 (fun z : Space (m + 1) ↦ z (Fin.last m)) :=
    (EuclideanSpace.proj (Fin.last m) : Space (m + 1) →L[ℝ] ℝ).contDiff
  have hη : ContDiff ℝ 1 η :=
    (b₁.contDiff.comp horizontalContinuousLinearMap.contDiff).mul (b₂.contDiff.comp hlast)
  have hsupp : ∀ z, η z ≠ 0 → ‖horizontal z‖ < 9 / 16 ∧ |z (Fin.last m)| < 5 / 8 := by
    intro z hz
    have h1 : b₁ (horizontal z) ≠ 0 := left_ne_zero_of_mul hz
    have h2 : b₂ (z (Fin.last m)) ≠ 0 := right_ne_zero_of_mul hz
    have h1' : horizontal z ∈ Function.support b₁ := h1
    have h2' : z (Fin.last m) ∈ Function.support b₂ := h2
    rw [b₁.support_eq, mem_ball, dist_zero_right] at h1'
    rw [b₂.support_eq, mem_ball, dist_zero_right, Real.norm_eq_abs] at h2'
    exact ⟨h1', h2'⟩
  have hclosed : IsClosed
      {z : Space (m + 1) | ‖horizontal z‖ ≤ 9 / 16 ∧ |z (Fin.last m)| ≤ 5 / 8} :=
    (isClosed_le continuous_horizontal.norm continuous_const).inter
      (isClosed_le hlastc.abs continuous_const)
  have hts : tsupport η ⊆
      {z : Space (m + 1) | ‖horizontal z‖ ≤ 9 / 16 ∧ |z (Fin.last m)| ≤ 5 / 8} := by
    refine closure_minimal (fun z hz ↦ ?_) hclosed
    have := hsupp z hz
    exact ⟨this.1.le, this.2.le⟩
  have htsball : tsupport η ⊆ closedBall (0 : Space (m + 1)) (19 / 16) := by
    intro z hz
    have h1 := hts hz
    have h2 := norm_le_norm_horizontal_add_abs_vertical z
    rw [mem_closedBall, dist_zero_right]
    linarith [h1.1, h1.2]
  have hηc : HasCompactSupport η :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport η) htsball
  obtain ⟨Cη, hCη⟩ := (hη.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hηc.fderiv (𝕜 := ℝ))
  refine ⟨η, hη, hηc, fun z ↦ ?_, fun z hz ↦ ?_, hsupp,
    htsball.trans (closedBall_subset_ball (by norm_num)), fun z hz ↦ (hts hz).2, Cη, hCη⟩
  · have h1 := b₁.nonneg (x := horizontal z)
    have h2 := b₂.nonneg (x := z (Fin.last m))
    have h1' := b₁.le_one (x := horizontal z)
    have h2' := b₂.le_one (x := z (Fin.last m))
    rw [abs_le]
    constructor <;> nlinarith
  · rw [mem_tiltCylinder_vertical_iff] at hz
    have h1 : b₁ (horizontal z) = 1 := b₁.one_of_mem_closedBall (by
      rw [mem_closedBall, dist_zero_right]
      exact hz.1.le.trans (by norm_num))
    have h2 : b₂ (z (Fin.last m)) = 1 := b₂.one_of_mem_closedBall (by
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      exact hz.2.le.trans (by norm_num))
    simp only [hηdef, h1, h2, mul_one]

/-- The height weight `w = ((t - a) / δ - H'(y)) η` is `C¹`, compactly supported inside the
support of `η`, with gradient at most `Cη ((5/8 + |a|) / δ + sup |H'|) + 1/δ + sup |DH'|`. -/
theorem heightMomentWeight_props {η : Space (m + 1) → ℝ} (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) (hη1 : ∀ z, |η z| ≤ 1)
    (hηt : ∀ z ∈ tsupport η, |z (Fin.last m)| ≤ 5 / 8) {Cη : ℝ}
    (hCη : ∀ z, ‖fderiv ℝ η z‖ ≤ Cη) {H' : Space m → ℝ} (hH' : ContDiff ℝ 1 H')
    {MH MH' : ℝ} (hMH : ∀ y, |H' y| ≤ MH) (hMH' : ∀ y, ‖fderiv ℝ H' y‖ ≤ MH') (a : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ 1 (fun z : Space (m + 1) ↦
        ((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z) ∧
      HasCompactSupport (fun z : Space (m + 1) ↦
        ((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z) ∧
      tsupport (fun z : Space (m + 1) ↦
        ((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z) ⊆ tsupport η ∧
      ∀ z, ‖gradient (fun z : Space (m + 1) ↦
        ((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z) z‖ ≤
          Cη * ((5 / 8 + |a|) / δ + MH) + (1 / δ + MH') := by
  set A : Space (m + 1) → ℝ := fun z ↦ (z (Fin.last m) - a) / δ - H' (horizontal z) with hAdef
  have hlast : ContDiff ℝ 1 (fun z : Space (m + 1) ↦ z (Fin.last m)) :=
    (EuclideanSpace.proj (Fin.last m) : Space (m + 1) →L[ℝ] ℝ).contDiff
  have hA : ContDiff ℝ 1 A :=
    ((hlast.sub contDiff_const).div_const δ).sub (hH'.comp horizontalContinuousLinearMap.contDiff)
  have hw : ContDiff ℝ 1 (fun z ↦ A z * η z) := hA.mul hη
  have hts : tsupport (fun z ↦ A z * η z) ⊆ tsupport η := tsupport_mul_subset_right
  have hwc : HasCompactSupport (fun z ↦ A z * η z) := hηc.mono' (subset_tsupport _ |>.trans hts)
  have hCη0 : 0 ≤ Cη := (norm_nonneg _).trans (hCη 0)
  have hMH0 : 0 ≤ MH := (abs_nonneg _).trans (hMH 0)
  have hMH'0 : 0 ≤ MH' := (norm_nonneg _).trans (hMH' 0)
  -- the Lipschitz bound of `A`
  have hA₁ : LipschitzWith (Real.toNNReal (1 / δ))
      (fun z : Space (m + 1) ↦ (z (Fin.last m) - a) / δ) := by
    apply LipschitzWith.of_dist_le_mul
    intro z z'
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity), dist_eq_norm,
      show (z (Fin.last m) - a) / δ - (z' (Fin.last m) - a) / δ =
        (z (Fin.last m) - z' (Fin.last m)) / δ by ring, abs_div, abs_of_pos hδ, div_eq_mul_inv,
      one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_last_sub_le_norm_ahm z z') (by positivity)
  have hH'L : LipschitzWith (Real.toNNReal MH') H' := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hH'.differentiable one_ne_zero)
    intro y
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hMH'0]
    exact hMH' y
  have hA₂ : LipschitzWith (Real.toNNReal MH' * 1) (fun z : Space (m + 1) ↦ H' (horizontal z)) :=
    hH'L.comp lipschitzWith_one_horizontal
  have hAL := hA₁.sub hA₂
  have hdA : ∀ z, ‖fderiv ℝ A z‖ ≤ 1 / δ + MH' := by
    intro z
    have h := norm_fderiv_le_of_lipschitz ℝ hAL (x₀ := z)
    have e1 : ((Real.toNNReal (1 / δ) + Real.toNNReal MH' * 1 : ℝ≥0) : ℝ) = 1 / δ + MH' := by
      rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, mul_one,
        Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hMH'0]
    rw [e1] at h
    exact h
  refine ⟨hw, hwc, hts, fun z ↦ ?_⟩
  by_cases hz : z ∈ tsupport η
  · have hfd : fderiv ℝ (fun z ↦ A z * η z) z = A z • fderiv ℝ η z + η z • fderiv ℝ A z :=
      fderiv_mul (hA.differentiable one_ne_zero z) (hη.differentiable one_ne_zero z)
    have hAz : |A z| ≤ (5 / 8 + |a|) / δ + MH := by
      have h1 : |(z (Fin.last m) - a) / δ| ≤ (5 / 8 + |a|) / δ := by
        rw [abs_div, abs_of_pos hδ]
        apply div_le_div_of_nonneg_right _ hδ.le
        calc |z (Fin.last m) - a| ≤ |z (Fin.last m)| + |a| := abs_sub _ _
          _ ≤ 5 / 8 + |a| := by linarith [hηt z hz]
      calc |A z| ≤ |(z (Fin.last m) - a) / δ| + |H' (horizontal z)| := abs_sub _ _
        _ ≤ (5 / 8 + |a|) / δ + MH := add_le_add h1 (hMH _)
    rw [gradient, LinearIsometryEquiv.norm_map, hfd]
    calc ‖A z • fderiv ℝ η z + η z • fderiv ℝ A z‖
        ≤ ‖A z • fderiv ℝ η z‖ + ‖η z • fderiv ℝ A z‖ := norm_add_le _ _
      _ = |A z| * ‖fderiv ℝ η z‖ + |η z| * ‖fderiv ℝ A z‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ((5 / 8 + |a|) / δ + MH) * Cη + 1 * (1 / δ + MH') :=
          add_le_add (mul_le_mul hAz (hCη z) (norm_nonneg _) (by positivity))
            (mul_le_mul (hη1 z) (hdA z) (norm_nonneg _) zero_le_one)
      _ = Cη * ((5 / 8 + |a|) / δ + MH) + (1 / δ + MH') := by ring
  · have hz' : z ∉ tsupport (fun z ↦ A z * η z) := fun h' ↦ hz (hts h')
    rw [gradient, fderiv_of_notMem_tsupport ℝ hz', map_zero, norm_zero]
    positivity

/-! ### HA6.1 at a single scale -/

/-- **The level-graph part at a single scale.** Over a subset `Db ⊆ B_{9/16}` of the horizontal
set of a level graph family, the weighted gradient mass of the level region is bounded by the
`L²(B_{9/16})` distance of the normalized height at any level `σ` to `H'`, up to `O(ε/δ)`. -/
theorem graphHeightMoment_le {v : Space (m + 1) → ℝ} {R δ a κ' c τ s₁ s₂ σ : ℝ} {L : ℝ≥0}
    {D Db : Set (Space m)} {hh : ℝ → Space m → ℝ} (hR : 0 < R) (hδ : 0 < δ) (hc : 0 < c)
    (hs : s₁ < s₂) (hG : LevelGraphFamily v D τ s₁ s₂ R c L hh) (hDbD : Db ⊆ D)
    (hDbm : MeasurableSet Db) (hDbB : Db ⊆ ball (0 : Space m) (9 / 16)) (hDne : D.Nonempty)
    (hσ : σ ∈ Icc s₁ s₂) (hgrad : ∀ z, ‖gradient v z‖ ≤ κ' * R)
    {η w : Space (m + 1) → ℝ} {H' : Space m → ℝ} (hwc : Continuous w) (hH'c : Continuous H')
    (hwdef : ∀ z, w z = ((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z)
    (hη1 : ∀ z, |η z| ≤ 1)
    (hint : IntegrableOn (fun z ↦ ‖gradient v z‖ ^ 2 / R * w z ^ 2) (levelRegion v Db τ s₁ s₂)) :
    (∫ z in levelRegion v Db τ s₁ s₂, ‖gradient v z‖ ^ 2 / R * w z ^ 2) ≤
      κ' ^ 2 / c * (s₂ - s₁) * (2 * ((s₂ - s₁) / (c * R * δ)) ^ 2 *
          volume.real (ball (0 : Space m) (9 / 16)) +
        2 * ∫ y in ball (0 : Space m) (9 / 16),
          (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H' y) ^ 2) := by
  set fσ := normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ with hfσdef
  set I := ∫ y in ball (0 : Space m) (9 / 16), (fσ y - H' y) ^ 2 with hIdef
  set V := volume.real (ball (0 : Space m) (9 / 16)) with hVdef
  set e := (s₂ - s₁) / (c * R * δ) with hedef
  have hs0 : 0 ≤ s₂ - s₁ := by linarith
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun y _ ↦ sq_nonneg _
  have hV0 : 0 ≤ V := measureReal_nonneg
  have hfσc : Continuous fσ :=
    ((hG.extendedHeight_lipschitzWith hs.le hDne σ).continuous.sub continuous_const).div_const δ
  have hIint : IntegrableOn (fun y ↦ (fσ y - H' y) ^ 2) (ball (0 : Space m) (9 / 16)) :=
    integrableOn_ball_of_continuous' ((hfσc.sub hH'c).pow 2) 0 _
  have hGb : LevelGraphFamily v Db τ s₁ s₂ R c L hh := hG.of_subset hDbD
  set Wg : Space m → ℝ := fun y ↦ 2 * (fσ y - H' y) ^ 2 + 2 * e ^ 2 with hWgdef
  have hWg : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ Db, w (point y (hh s y)) ^ 2 ≤ Wg y := by
    intro s hs' y hy
    have hext : extendedHeight D L τ s₁ s₂ hh s y = hh s y := hG.extendedHeight_eq hs' (hDbD hy)
    have hd := hG.abs_normalizedHeight_sub_le_of_mem hR hc hs.le hDne hδ a hs' hσ y
    rw [normalizedHeight, hext] at hd
    rw [hwdef, horizontal_point, last_point, mul_pow]
    have hη2 : η (point y (hh s y)) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (hη1 _)
    have hd2 : ((hh s y - a) / δ - fσ y) ^ 2 ≤ e ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    have hA2 : ((hh s y - a) / δ - H' y) ^ 2 ≤ Wg y := by
      simp only [hWgdef]
      nlinarith [sq_nonneg (((hh s y - a) / δ - fσ y) - (fσ y - H' y))]
    calc ((hh s y - a) / δ - H' y) ^ 2 * η (point y (hh s y)) ^ 2
        ≤ ((hh s y - a) / δ - H' y) ^ 2 * 1 := mul_le_mul_of_nonneg_left hη2 (sq_nonneg _)
      _ ≤ Wg y := by rw [mul_one]; exact hA2
  have hWg0 : ∀ y, 0 ≤ Wg y := fun y ↦ by positivity
  have hWgint : IntegrableOn Wg (ball (0 : Space m) (9 / 16)) :=
    (hIint.const_mul 2).add (integrableOn_const measure_ball_lt_top.ne)
  have hWgball : ∫ y in ball (0 : Space m) (9 / 16), Wg y = 2 * I + 2 * e ^ 2 * V := by
    simp only [hWgdef]
    rw [integral_add (hIint.const_mul 2) (integrableOn_const measure_ball_lt_top.ne),
      integral_const_mul, setIntegral_const, smul_eq_mul]
    ring
  have hlin := hGb.lintegral_levelRegion_weighted_le hR hc hs.le hDbm hgrad hwc.measurable hWg
  have hlD : ∫⁻ y in Db, ENNReal.ofReal (Wg y) ≤ ENNReal.ofReal (2 * I + 2 * e ^ 2 * V) := by
    rw [← hWgball, ofReal_integral_eq_lintegral_ofReal hWgint (ae_of_all _ hWg0)]
    exact lintegral_mono_set hDbB
  have hK0 : 0 ≤ κ' ^ 2 / c * (s₂ - s₁) := by positivity
  have hfin : ENNReal.ofReal (κ' ^ 2 / c * (s₂ - s₁)) * ENNReal.ofReal (2 * I + 2 * e ^ 2 * V) ≠
      ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hstep : (∫⁻ z in levelRegion v Db τ s₁ s₂,
      ENNReal.ofReal (‖gradient v z‖ ^ 2 / R * w z ^ 2)) ≤
      ENNReal.ofReal (κ' ^ 2 / c * (s₂ - s₁)) * ENNReal.ofReal (2 * I + 2 * e ^ 2 * V) :=
    hlin.trans (mul_le_mul' le_rfl hlD)
  have heq : (ENNReal.ofReal (κ' ^ 2 / c * (s₂ - s₁)) *
      ENNReal.ofReal (2 * I + 2 * e ^ 2 * V)).toReal =
      κ' ^ 2 / c * (s₂ - s₁) * (2 * e ^ 2 * V + 2 * I) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0, ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z ↦ by positivity)
    hint.aestronglyMeasurable, ← heq]
  exact ENNReal.toReal_mono hfin hstep

/-- **The low good points at a single scale.** If the points of a measurable set `S` over
`Db ⊆ B_{9/16}` lie within `Λ / R` of the shifted `s₁`-level height and carry `ρ ≤ Md R`, their
weighted gradient mass is bounded by the `L²(B_{9/16})` distance of the normalized height at any
level `σ` to `H'`, up to `O(ε/δ)`. -/
theorem lowHeightMoment_le {v : Space (m + 1) → ℝ} {R δ a c τ s₁ s₂ σ Λ Md T₁ : ℝ}
    {L : ℝ≥0} {D Db : Set (Space m)} {hh : ℝ → Space m → ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hc : 0 < c) (hs : s₁ < s₂) (hG : LevelGraphFamily v D τ s₁ s₂ R c L hh) (hDbD : Db ⊆ D)
    (hDbm : MeasurableSet Db) (hDbB : Db ⊆ ball (0 : Space m) (9 / 16)) (hDne : D.Nonempty)
    (hσ : σ ∈ Icc s₁ s₂) (hΛ : 0 ≤ Λ) (hMd : 0 ≤ Md) (hT₁ : 0 ≤ T₁)
    {S : Set (Space (m + 1))} (hSm : MeasurableSet S) (hSD : ∀ p ∈ S, horizontal p ∈ Db)
    {η w : Space (m + 1) → ℝ} {H' : Space m → ℝ} (hwc : Continuous w) (hH'c : Continuous H')
    (hwdef : ∀ z, w z = ((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z)
    (hη1 : ∀ z, |η z| ≤ 1)
    (hband : ∀ p ∈ S, |p (Fin.last m) - (hh s₁ (horizontal p) - T₁ / R)| ≤ Λ / R)
    (hdens : ∀ p ∈ S, ‖gradient v p‖ ^ 2 / R ≤ Md * R) :
    (∫ z in S, ‖gradient v z‖ ^ 2 / R * w z ^ 2) ≤
      2 * Λ * Md * ((2 * (Λ / (R * δ)) ^ 2 +
          4 * ((s₂ - s₁) / (c * R * δ) + T₁ / (R * δ)) ^ 2) *
          volume.real (ball (0 : Space m) (9 / 16)) +
        4 * ∫ y in ball (0 : Space m) (9 / 16),
          (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H' y) ^ 2) := by
  set fσ := normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ with hfσdef
  set I := ∫ y in ball (0 : Space m) (9 / 16), (fσ y - H' y) ^ 2 with hIdef
  set V := volume.real (ball (0 : Space m) (9 / 16)) with hVdef
  set e := (s₂ - s₁) / (c * R * δ) with hedef
  have hfσc : Continuous fσ :=
    ((hG.extendedHeight_lipschitzWith hs.le hDne σ).continuous.sub continuous_const).div_const δ
  have hIint : IntegrableOn (fun y ↦ (fσ y - H' y) ^ 2) (ball (0 : Space m) (9 / 16)) :=
    integrableOn_ball_of_continuous' ((hfσc.sub hH'c).pow 2) 0 _
  set F : Space (m + 1) → ℝ := fun z ↦ ‖gradient v z‖ ^ 2 / R * w z ^ 2 with hFdef
  have hF0 : ∀ z, 0 ≤ F z := fun z ↦ by positivity
  have hFm : Measurable F :=
    (((measurable_gradient v).norm.pow_const 2).div_const R).mul (hwc.measurable.pow_const 2)
  set ext₁ := extendedHeight D L τ s₁ s₂ hh s₁ with hext₁def
  have hext₁c : Continuous ext₁ := (hG.extendedHeight_lipschitzWith hs.le hDne s₁).continuous
  set cf : Space m → ℝ := fun y ↦ ext₁ y - T₁ / R with hcfdef
  set Wl : Space m → ℝ := fun y ↦ 2 * (Λ / (R * δ)) ^ 2 + 2 * ((cf y - a) / δ - H' y) ^ 2
    with hWldef
  have hWlc : Continuous Wl :=
    continuous_const.add (continuous_const.mul
      (((((hext₁c.sub continuous_const).sub continuous_const).div_const δ).sub hH'c).pow 2))
  have hWlint : IntegrableOn Wl Db :=
    (integrableOn_ball_of_continuous' hWlc 0 (9 / 16)).mono_set hDbB
  have hK0 : ∀ y ∈ Db, 0 ≤ Md * R * Wl y := fun y _ ↦ by positivity
  have hband' : ∀ y ∈ Db, ∀ t, point y t ∈ S →
      |t - cf y| ≤ Λ / R ∧ F (point y t) ≤ Md * R * Wl y := by
    intro y hy t hpS
    have hcy : cf y = hh s₁ y - T₁ / R := by
      simp only [hcfdef, hext₁def, hG.extendedHeight_eq ⟨le_rfl, hs.le⟩ (hDbD hy)]
    have hb := hband (point y t) hpS
    rw [horizontal_point, last_point] at hb
    have hbt : |t - cf y| ≤ Λ / R := by rw [hcy]; exact hb
    refine ⟨hbt, ?_⟩
    have hdp := hdens (point y t) hpS
    have hw2 : w (point y t) ^ 2 ≤ Wl y := by
      rw [hwdef, horizontal_point, last_point, mul_pow]
      have hη2 : η (point y t) ^ 2 ≤ 1 := by
        rw [← sq_abs]
        exact pow_le_one₀ (abs_nonneg _) (hη1 _)
      have hband2 : ((t - cf y) / δ) ^ 2 ≤ (Λ / (R * δ)) ^ 2 := by
        have h1 : (t - cf y) ^ 2 ≤ (Λ / R) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hbt 2
        have h2 : (Λ / (R * δ)) ^ 2 = (Λ / R) ^ 2 / δ ^ 2 := by
          rw [div_pow, div_pow, mul_pow, div_div]
        rw [h2, div_pow]
        exact div_le_div_of_nonneg_right h1 (by positivity)
      have hA2 : ((t - a) / δ - H' y) ^ 2 ≤ Wl y := by
        have hsplit : (t - a) / δ - H' y = (t - cf y) / δ + ((cf y - a) / δ - H' y) := by
          ring
        rw [hsplit]
        simp only [hWldef]
        nlinarith [sq_nonneg ((t - cf y) / δ - ((cf y - a) / δ - H' y))]
      calc _ ≤ ((t - a) / δ - H' y) ^ 2 * 1 := mul_le_mul_of_nonneg_left hη2 (sq_nonneg _)
        _ ≤ Wl y := by rw [mul_one]; exact hA2
    show ‖gradient v (point y t)‖ ^ 2 / R * w (point y t) ^ 2 ≤ Md * R * Wl y
    exact mul_le_mul hdp hw2 (sq_nonneg _) (by positivity)
  have hvb := setIntegral_le_of_vertical_band hSm hFm hF0 hDbm hSD
    (div_nonneg hΛ hR.le) hK0 (hWlint.const_mul (Md * R)) hband'
  set Wbd : Space m → ℝ := fun y ↦ 2 * (Λ / (R * δ)) ^ 2 + 4 * (e + T₁ / (R * δ)) ^ 2 +
    4 * (fσ y - H' y) ^ 2 with hWbddef
  have hWlbd : ∀ y, Wl y ≤ Wbd y := by
    intro y
    have hd := hG.abs_normalizedHeight_sub_le_of_mem hR hc hs.le hDne hδ a
      ⟨le_rfl, hs.le⟩ hσ y
    have hx : (cf y - a) / δ - H' y =
        (normalizedHeight ext₁ a δ y - fσ y - T₁ / (R * δ)) + (fσ y - H' y) := by
      simp only [hcfdef, normalizedHeight]
      field_simp
      ring
    have hT0 : 0 ≤ T₁ / (R * δ) := by positivity
    have hx2 : (normalizedHeight ext₁ a δ y - fσ y - T₁ / (R * δ)) ^ 2 ≤
        (e + T₁ / (R * δ)) ^ 2 := by
      rw [← sq_abs]
      apply pow_le_pow_left₀ (abs_nonneg _)
      calc |normalizedHeight ext₁ a δ y - fσ y - T₁ / (R * δ)|
          ≤ |normalizedHeight ext₁ a δ y - fσ y| + |T₁ / (R * δ)| := abs_sub _ _
        _ ≤ e + T₁ / (R * δ) := by rw [abs_of_nonneg hT0]; linarith [hd]
    simp only [hWldef, hWbddef]
    rw [hx]
    nlinarith [sq_nonneg ((normalizedHeight ext₁ a δ y - fσ y - T₁ / (R * δ)) -
      (fσ y - H' y))]
  have hcI : IntegrableOn (fun _ : Space m ↦ 2 * (Λ / (R * δ)) ^ 2 +
      4 * (e + T₁ / (R * δ)) ^ 2) (ball (0 : Space m) (9 / 16)) :=
    integrableOn_const measure_ball_lt_top.ne
  have hWbdint : IntegrableOn Wbd (ball (0 : Space m) (9 / 16)) := hcI.add (hIint.const_mul 4)
  have hWbdball : ∫ y in ball (0 : Space m) (9 / 16), Wbd y =
      (2 * (Λ / (R * δ)) ^ 2 + 4 * (e + T₁ / (R * δ)) ^ 2) * V + 4 * I := by
    simp only [hWbddef]
    rw [integral_add hcI (hIint.const_mul 4), setIntegral_const, smul_eq_mul, integral_const_mul]
    ring
  have hstep : ∫ y in Db, Wl y ≤
      (2 * (Λ / (R * δ)) ^ 2 + 4 * (e + T₁ / (R * δ)) ^ 2) * V + 4 * I := by
    rw [← hWbdball]
    calc ∫ y in Db, Wl y ≤ ∫ y in Db, Wbd y :=
          setIntegral_mono_on hWlint (hWbdint.mono_set hDbB) hDbm fun y _ ↦ hWlbd y
      _ ≤ ∫ y in ball (0 : Space m) (9 / 16), Wbd y :=
          setIntegral_mono_set hWbdint (ae_of_all _ fun y ↦ by positivity)
            (Eventually.of_forall hDbB)
  have hfac : 2 * (Λ / R) * ∫ y in Db, Md * R * Wl y = 2 * Λ * Md * ∫ y in Db, Wl y := by
    rw [integral_const_mul]
    field_simp
  calc (∫ z in S, F z) ≤ 2 * (Λ / R) * ∫ y in Db, Md * R * Wl y := hvb
    _ = 2 * Λ * Md * ∫ y in Db, Wl y := hfac
    _ ≤ 2 * Λ * Md * ((2 * (Λ / (R * δ)) ^ 2 + 4 * (e + T₁ / (R * δ)) ^ 2) * V + 4 * I) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)

/-- **The tilt-bad points at a single scale.** On the transition layer `|t| < δ''` over
`|y| < 9/16`, the weight is at most `2 (δ'' + |a|)²/δ² + 2 sup |H'|²`, and the bad points carry
gradient mass at most `CB`. -/
theorem badHeightMoment_le {v : Space (m + 1) → ℝ} {R δ a κ' : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hgrad : ∀ z, ‖gradient v z‖ ≤ κ' * R)
    {η w : Space (m + 1) → ℝ} {H' : Space m → ℝ}
    (hwdef : ∀ z, w z = ((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z)
    (hη1 : ∀ z, |η z| ≤ 1) {MH : ℝ} (hMH : ∀ y, |H' y| ≤ MH)
    (hint : Integrable (fun z ↦ ‖gradient v z‖ ^ 2 / R * w z ^ 2)) {δ'' r₀ ℓb : ℝ}
    (hδ''58 : δ'' ≤ 5 / 8) {B : Set (Space (m + 1))} (hBm : MeasurableSet B)
    (hB : ∀ z ∈ B, ‖horizontal z‖ < 9 / 16 ∧ |z (Fin.last m)| < δ'' ∧
      ∃ r ∈ Ioc 0 (2 * r₀), ℓb * r ^ m ≤
        ∫ y in ball z r, diffuseTiltDensity R v (verticalDirection m) y)
    {CB : ℝ≥0∞} (hCB : CB ≠ ⊤)
    (hbad : ∫⁻ p in {p | ∃ r : ℝ, 0 < r ∧ r ≤ 2 * r₀ ∧
        ball p r ⊆ closedBall (0 : Space (m + 1)) (19 / 16 + 2 * r₀) ∧
        ℓb * r ^ m ≤ ∫ y in ball p r, diffuseTiltDensity R v (verticalDirection m) y},
        ENNReal.ofReal (‖gradient v p‖ ^ 2 / R) ≤ CB) :
    (∫ z in B, ‖gradient v z‖ ^ 2 / R * w z ^ 2) ≤
      (2 * (δ'' + |a|) ^ 2 / δ ^ 2 + 2 * MH ^ 2) * CB.toReal := by
  set Wb := 2 * (δ'' + |a|) ^ 2 / δ ^ 2 + 2 * MH ^ 2 with hWbdef
  have hWb0 : 0 ≤ Wb := by positivity
  have hBball : B ⊆ ball (0 : Space (m + 1)) 2 := by
    intro z hz
    have := norm_le_norm_horizontal_add_abs_vertical z
    rw [mem_ball, dist_zero_right]
    linarith [(hB z hz).1, (hB z hz).2.1]
  have hρint : IntegrableOn (fun z ↦ ‖gradient v z‖ ^ 2 / R) B := by
    refine (Measure.integrableOn_of_bounded (M := (κ' * R) ^ 2 / R)
      (measure_ball_lt_top (x := (0 : Space (m + 1))) (r := 2)).ne
      (((measurable_gradient v).norm.pow_const 2).div_const R).aestronglyMeasurable ?_).mono_set
      hBball
    refine Eventually.of_forall fun z ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hgrad z) 2) hR.le
  have hsubbad : B ⊆ {p | ∃ r : ℝ, 0 < r ∧ r ≤ 2 * r₀ ∧
      ball p r ⊆ closedBall (0 : Space (m + 1)) (19 / 16 + 2 * r₀) ∧
      ℓb * r ^ m ≤ ∫ y in ball p r, diffuseTiltDensity R v (verticalDirection m) y} := by
    intro p hp
    obtain ⟨hp1, hp2, r, hr, hrle⟩ := hB p hp
    refine ⟨r, hr.1, hr.2, fun z hz ↦ ?_, hrle⟩
    have hpn : ‖p‖ < 19 / 16 := by
      have := norm_le_norm_horizontal_add_abs_vertical p
      linarith
    rw [mem_closedBall, dist_zero_right]
    rw [mem_ball, dist_eq_norm] at hz
    have := norm_le_norm_add_norm_sub' z p
    linarith [hr.2]
  calc (∫ z in B, ‖gradient v z‖ ^ 2 / R * w z ^ 2)
      ≤ ∫ z in B, Wb * (‖gradient v z‖ ^ 2 / R) := by
        refine setIntegral_mono_on hint.integrableOn (hρint.const_mul Wb) hBm fun z hz ↦ ?_
        obtain ⟨hz1, hz2, -⟩ := hB z hz
        have hA : ((z (Fin.last m) - a) / δ - H' (horizontal z)) ^ 2 ≤ Wb := by
          have h1 : |z (Fin.last m) - a| ≤ δ'' + |a| :=
            (abs_sub _ _).trans (by linarith [hz2.le])
          have h3 : ((z (Fin.last m) - a) / δ) ^ 2 ≤ (δ'' + |a|) ^ 2 / δ ^ 2 := by
            rw [div_pow]
            apply div_le_div_of_nonneg_right _ (by positivity)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          have h4 : H' (horizontal z) ^ 2 ≤ MH ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hMH _) 2
          have h5 : ((z (Fin.last m) - a) / δ - H' (horizontal z)) ^ 2 ≤
              2 * ((z (Fin.last m) - a) / δ) ^ 2 + 2 * H' (horizontal z) ^ 2 := by
            nlinarith [sq_nonneg ((z (Fin.last m) - a) / δ + H' (horizontal z))]
          calc ((z (Fin.last m) - a) / δ - H' (horizontal z)) ^ 2
              ≤ 2 * ((z (Fin.last m) - a) / δ) ^ 2 + 2 * H' (horizontal z) ^ 2 := h5
            _ ≤ 2 * ((δ'' + |a|) ^ 2 / δ ^ 2) + 2 * MH ^ 2 := by linarith
            _ = Wb := by rw [hWbdef]; ring
        have hw2 : w z ^ 2 ≤ Wb := by
          rw [hwdef z, mul_pow]
          have : η z ^ 2 ≤ 1 := by
            rw [← sq_abs]
            exact pow_le_one₀ (abs_nonneg _) (hη1 z)
          calc _ ≤ ((z (Fin.last m) - a) / δ - H' (horizontal z)) ^ 2 * 1 :=
                mul_le_mul_of_nonneg_left this (sq_nonneg _)
            _ ≤ Wb := by rw [mul_one]; exact hA
        show ‖gradient v z‖ ^ 2 / R * w z ^ 2 ≤ Wb * (‖gradient v z‖ ^ 2 / R)
        rw [mul_comm Wb]
        exact mul_le_mul_of_nonneg_left hw2 (by positivity)
    _ = Wb * ∫ z in B, ‖gradient v z‖ ^ 2 / R := integral_const_mul _ _
    _ ≤ Wb * CB.toReal := by
        apply mul_le_mul_of_nonneg_left _ hWb0
        rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z ↦ by positivity)
          hρint.aestronglyMeasurable]
        exact ENNReal.toReal_mono hCB ((lintegral_mono_set hsubbad).trans hbad)

/-- **HA6.1 at a single scale: the transition region.** Let `v ≥ 0` with `|∇v| ≤ κ' R`, and let
`w = ((t - a)/δ - H'(y)) η` be a height weight with `|η| ≤ 1` supported in `|y| < 9/16`,
`|t| < 5/8`. Suppose the transition points `0 < v < s₂` of the support of `η` lie in the thin layer
`|t| < δ''`, the good points (threshold `ℓ`, height `< 1`) project into `D`, `v` has a level graph
family over `D` for the levels `[s₁, s₂]`, the low good points (threshold `ℓb ≤ ℓ`) lie within
`Λ / R` of the shifted `s₁`-level height, `ρ = |∇v|² / R ≤ Md R` on the positive phase, and the
bad points (threshold `ℓb`) carry gradient mass at most `CB`. Then `∫_{v < s₂} ρ w²` is bounded by
the bad mass, the `L²(B_{9/16})` distance of the normalized height at any level `σ ∈ [s₁, s₂]`
to `H'`, and terms of order `ε / δ`. -/
theorem transitionHeightMoment_le {v : Space (m + 1) → ℝ} (hvc : Continuous v)
    (hv0 : ∀ z, 0 ≤ v z) {R δ a κ' : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hgrad : ∀ z, ‖gradient v z‖ ≤ κ' * R)
    {η w : Space (m + 1) → ℝ} {H' : Space m → ℝ} (hηc : Continuous η) (hH'c : Continuous H')
    (hwdef : ∀ z, w z = ((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z)
    (hη1 : ∀ z, |η z| ≤ 1)
    (hηsupp : ∀ z, η z ≠ 0 → ‖horizontal z‖ < 9 / 16 ∧ |z (Fin.last m)| < 5 / 8)
    {MH : ℝ} (hMH : ∀ y, |H' y| ≤ MH)
    (hint : Integrable (fun z ↦ ‖gradient v z‖ ^ 2 / R * w z ^ 2))
    {δ'' τ s₁ s₂ : ℝ} (hδ''τ : δ'' ≤ τ) (hδ''58 : δ'' ≤ 5 / 8)
    (hthin : ∀ z, ‖horizontal z‖ < 9 / 16 → |z (Fin.last m)| < 5 / 8 → 0 < v z → v z < s₂ →
      |z (Fin.last m)| < δ'')
    {D : Set (Space m)} (hDo : IsOpen D) {ℓ ℓb r₀ b ρ : ℝ} (hρ : 9 / 16 < ρ)
    (hℓbℓ : ℓb ≤ ℓ)
    (hgood : ∀ p, IsLayerGoodPoint R v (verticalDirection m) ℓ r₀ b p → |p (Fin.last m)| < 1 →
      ‖horizontal p‖ < ρ → horizontal p ∈ D)
    (hbs₂ : s₂ ≤ 1 - b) {c : ℝ} {L : ℝ≥0} (hc : 0 < c) (hs : s₁ < s₂)
    {hh : ℝ → Space m → ℝ} (hG : LevelGraphFamily v D τ s₁ s₂ R c L hh)
    {σ : ℝ} (hσ : σ ∈ Icc s₁ s₂) {Λ Md T₁ : ℝ} (hΛ : 0 ≤ Λ) (hMd : 0 ≤ Md) (hT₁ : 0 ≤ T₁)
    (hlowband : ∀ p, horizontal p ∈ D → ‖horizontal p‖ < 9 / 16 → |p (Fin.last m)| < δ'' →
      0 < v p → v p < s₁ →
      (∀ r ∈ Ioc 0 (2 * r₀), ∫ z in ball p r, diffuseTiltDensity R v (verticalDirection m) z <
        ℓb * r ^ m) →
      |p (Fin.last m) - (hh s₁ (horizontal p) - T₁ / R)| ≤ Λ / R)
    (hdens : ∀ p, 0 < v p → ‖gradient v p‖ ^ 2 / R ≤ Md * R)
    {CB : ℝ≥0∞} (hCB : CB ≠ ⊤)
    (hbad : ∫⁻ p in {p | ∃ r : ℝ, 0 < r ∧ r ≤ 2 * r₀ ∧
        ball p r ⊆ closedBall (0 : Space (m + 1)) (19 / 16 + 2 * r₀) ∧
        ℓb * r ^ m ≤ ∫ y in ball p r, diffuseTiltDensity R v (verticalDirection m) y},
        ENNReal.ofReal (‖gradient v p‖ ^ 2 / R) ≤ CB) :
    (∫ z in {z | v z < s₂}, ‖gradient v z‖ ^ 2 / R * w z ^ 2) ≤
      (2 * (δ'' + |a|) ^ 2 / δ ^ 2 + 2 * MH ^ 2) * CB.toReal +
      κ' ^ 2 / c * (s₂ - s₁) * (2 * ((s₂ - s₁) / (c * R * δ)) ^ 2 *
          volume.real (ball (0 : Space m) (9 / 16)) +
        2 * ∫ y in ball (0 : Space m) (9 / 16),
          (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H' y) ^ 2) +
      2 * Λ * Md * ((2 * (Λ / (R * δ)) ^ 2 +
          4 * ((s₂ - s₁) / (c * R * δ) + T₁ / (R * δ)) ^ 2) *
          volume.real (ball (0 : Space m) (9 / 16)) +
        4 * ∫ y in ball (0 : Space m) (9 / 16),
          (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H' y) ^ 2) := by
  classical
  have hlastc : Continuous (fun z : Space (m + 1) ↦ z (Fin.last m)) :=
    (EuclideanSpace.proj (Fin.last m) : Space (m + 1) →L[ℝ] ℝ).continuous
  have hwc : Continuous w := by
    have hweq : w = fun z ↦ ((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z := funext hwdef
    rw [hweq]
    exact (((hlastc.sub continuous_const).div_const δ).sub
      (hH'c.comp continuous_horizontal)).mul hηc
  set F : Space (m + 1) → ℝ := fun z ↦ ‖gradient v z‖ ^ 2 / R * w z ^ 2 with hFdef
  have hF0 : ∀ z, 0 ≤ F z := fun z ↦ by positivity
  -- step 1: localization to the thin transition layer
  set Es : Set (Space (m + 1)) := {z | 0 < v z ∧ v z < s₂ ∧ ‖horizontal z‖ < 9 / 16 ∧
    |z (Fin.last m)| < δ''} with hEsdef
  have hEm : MeasurableSet {z : Space (m + 1) | v z < s₂} :=
    measurableSet_lt hvc.measurable measurable_const
  have hEsm : MeasurableSet Es :=
    (measurableSet_lt measurable_const hvc.measurable).inter
      ((measurableSet_lt hvc.measurable measurable_const).inter
        ((measurableSet_lt continuous_horizontal.norm.measurable measurable_const).inter
          (measurableSet_lt hlastc.abs.measurable measurable_const)))
  have hzero : ∀ z ∈ {z : Space (m + 1) | v z < s₂} \ Es, F z = 0 := by
    rintro z ⟨hzE, hzn⟩
    by_cases hv : v z ≤ 0
    · have hvz : v z = 0 := le_antisymm hv (hv0 z)
      have hmin : IsLocalMin v z := Filter.Eventually.of_forall fun y ↦ by rw [hvz]; exact hv0 y
      have hgz : gradient v z = 0 := by simp only [gradient, hmin.fderiv_eq_zero, map_zero]
      simp [hFdef, hgz]
    · push Not at hv
      by_cases hη : η z = 0
      · simp [hFdef, hwdef z, hη]
      · obtain ⟨h1, h2⟩ := hηsupp z hη
        exact absurd ⟨hv, hzE, h1, hthin z h1 h2 hv hzE⟩ hzn
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hEm (fun z hz ↦ hz.2.1) hzero]
  -- step 2: tilt-good and tilt-bad points
  set tilt : Space (m + 1) → ℝ := diffuseTiltDensity R v (verticalDirection m) with htiltdef
  have htm : Measurable tilt := measurable_diffuseTiltDensity R v _
  have ht0 : ∀ z, 0 ≤ tilt z := fun z ↦
    diffuseTiltDensity_nonneg hR v (norm_verticalDirection m) z
  have htC : ∀ z, tilt z ≤ (κ' * R) ^ 2 / R := by
    intro z
    simp only [htiltdef, diffuseTiltDensity]
    apply div_le_div_of_nonneg_right _ hR.le
    have h1 : ‖gradient v z‖ ^ 2 ≤ (κ' * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hgrad z) 2
    nlinarith [sq_nonneg (inner ℝ (gradient v z) (verticalDirection m))]
  set Gd : Set (Space (m + 1)) :=
    {p | ∀ r ∈ Ioc 0 (2 * r₀), ∫ y in ball p r, tilt y < ℓb * r ^ m} with hGddef
  have hGdm : MeasurableSet Gd :=
    (isOpen_setOf_forall_setIntegral_ball_lt htm ht0 htC ℓb (2 * r₀)).measurableSet
  have hsplit₁ := integral_inter_add_sdiff (μ := volume) hGdm (hint.integrableOn (s := Es))
  -- step 3: the bad points
  have hbadpart := badHeightMoment_le hR hδ hgrad hwdef hη1 hMH hint hδ''58
    (hEsm.diff hGdm) (fun z hz ↦ ⟨hz.1.2.2.1, hz.1.2.2.2, by
      have hzG := hz.2
      by_contra hn
      push Not at hn
      exact hzG hn⟩) hCB hbad
  -- step 4: the good points project into the good set
  set Db := D ∩ ball (0 : Space m) (9 / 16) with hDbdef
  have hDbo : IsOpen Db := hDo.inter isOpen_ball
  have hgoodp : ∀ p ∈ Es ∩ Gd, horizontal p ∈ Db := by
    rintro p ⟨hpE, hpG⟩
    have hgp : IsLayerGoodPoint R v (verticalDirection m) ℓ r₀ b p := by
      refine ⟨⟨hpE.1, by linarith [hpE.2.1]⟩, fun r hr ↦ ?_⟩
      have := hpG r ⟨hr.1, by linarith [hr.2, hr.1]⟩
      exact this.trans_le (mul_le_mul_of_nonneg_right hℓbℓ (pow_nonneg hr.1.le m))
    exact ⟨hgood p hgp (by linarith [hpE.2.2.2]) (by linarith [hpE.2.2.1]),
      by rw [mem_ball, dist_zero_right]; exact hpE.2.2.1⟩
  set Ev : Set (Space (m + 1)) := {z | s₁ ≤ v z} with hEvdef
  have hEvm : MeasurableSet Ev := measurableSet_le measurable_const hvc.measurable
  have hsplit₂ := integral_inter_add_sdiff (μ := volume) hEvm
    (hint.integrableOn (s := Es ∩ Gd))
  have hs0 : 0 ≤ s₂ - s₁ := by linarith
  have hI0 : 0 ≤ ∫ y in ball (0 : Space m) (9 / 16),
      (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H' y) ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun y _ ↦ sq_nonneg _
  have hV0 : 0 ≤ volume.real (ball (0 : Space m) (9 / 16)) := measureReal_nonneg
  have hrest0 : 0 ≤ κ' ^ 2 / c * (s₂ - s₁) * (2 * ((s₂ - s₁) / (c * R * δ)) ^ 2 *
      volume.real (ball (0 : Space m) (9 / 16)) +
      2 * ∫ y in ball (0 : Space m) (9 / 16),
        (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H' y) ^ 2) := by positivity
  have hrest1 : 0 ≤ 2 * Λ * Md * ((2 * (Λ / (R * δ)) ^ 2 +
      4 * ((s₂ - s₁) / (c * R * δ) + T₁ / (R * δ)) ^ 2) *
      volume.real (ball (0 : Space m) (9 / 16)) +
      4 * ∫ y in ball (0 : Space m) (9 / 16),
        (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H' y) ^ 2) := by positivity
  rcases Db.eq_empty_or_nonempty with hDb | hDbne
  · have hempty : Es ∩ Gd = ∅ := by
      ext p
      simp only [mem_empty_iff_false, iff_false]
      intro hp
      have := hgoodp p hp
      rw [hDb] at this
      exact this
    have h0 : ∫ z in Es ∩ Gd, F z = 0 := by
      rw [hempty, Measure.restrict_empty, integral_zero_measure]
    linarith [hbadpart]
  obtain ⟨y₀, hy₀⟩ := hDbne
  have hDne : D.Nonempty := ⟨y₀, hy₀.1⟩
  -- step 5: the level-graph part
  have hLR : Es ∩ Gd ∩ Ev ⊆ levelRegion v Db τ s₁ s₂ := by
    rintro p ⟨hpEG, hpv⟩
    have hpn := hpEG.1.2.2.2
    rw [abs_lt] at hpn
    exact ⟨hgoodp p hpEG, ⟨by linarith, by linarith⟩, hpv, hpEG.1.2.1.le⟩
  have hgraph := graphHeightMoment_le (σ := σ) (a := a) hR hδ hc hs hG inter_subset_left
    hDbo.measurableSet inter_subset_right hDne hσ hgrad hwc hH'c hwdef hη1 hint.integrableOn
  have hgraph' : (∫ z in Es ∩ Gd ∩ Ev, F z) ≤ ∫ z in levelRegion v Db τ s₁ s₂, F z :=
    setIntegral_mono_set hint.integrableOn (ae_of_all _ hF0) (Eventually.of_forall hLR)
  -- step 6: the low good points
  have hlow := lowHeightMoment_le (σ := σ) (a := a) (Λ := Λ) (Md := Md) (T₁ := T₁) hR hδ hc hs
    hG inter_subset_left hDbo.measurableSet inter_subset_right hDne hσ hΛ hMd hT₁
    ((hEsm.inter hGdm).diff hEvm) (fun p hp ↦ hgoodp p hp.1) hwc hH'c hwdef hη1
    (fun p hp ↦ by
      have hpE := hp.1.1
      have hpD := hgoodp p hp.1
      exact hlowband p hpD.1 hpE.2.2.1 hpE.2.2.2 hpE.1 (lt_of_not_ge hp.2) hp.1.2)
    (fun p hp ↦ hdens p hp.1.1.1)
  linarith [hbadpart, hgraph, hgraph', hlow, hsplit₁, hsplit₂]

/-! ### HA6.1 for a rotated rescaled translate -/

theorem abs_sub_le_div_of_band {R t H A B : ℝ} (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : -A < R * (t - H)) (h2 : R * (t - H) < B) : |t - H| ≤ (A + B) / R := by
  have habs : |R * (t - H)| ≤ A + B := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_of_pos hR] at habs
  rw [le_div_iff₀ hR]
  linarith [mul_comm R |t - H|]

/-- **HA6.1 at a single scale for `v = U(x₀ + R • Q ·)`.** Combines the weight `w` (cutoff `η`,
regular height `H'`), the HA5 total bound for `w`, and the transition estimate
`transitionHeightMoment_le` with the HA1.1 bad-set bound; the result is written in terms of
`(R δ)⁻¹`, `R⁻¹`, `|a|`, `δ` and the `L²(B_{9/16})` distance of the normalized height at level
`σ` to the `L²` limit `H`. -/
theorem RigidityHypotheses.heightMoment_le_of_scale (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {x₀ : Space (m + 1)} {R δ a : ℝ} {Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    (hR : 0 < R) (hδ : 0 < δ)
    {η : Space (m + 1) → ℝ} (hη1c : ContDiff ℝ 1 η) (hηcs : HasCompactSupport η)
    (hη1 : ∀ z, |η z| ≤ 1) (hηQ : ∀ z ∈ tiltCylinder (verticalDirection m) (1 / 2), η z = 1)
    (hηsupp : ∀ z, η z ≠ 0 → ‖horizontal z‖ < 9 / 16 ∧ |z (Fin.last m)| < 5 / 8)
    (hηts : tsupport η ⊆ ball (0 : Space (m + 1)) (5 / 4))
    (hηtsl : ∀ z ∈ tsupport η, |z (Fin.last m)| ≤ 5 / 8) {Cη : ℝ}
    (hCη : ∀ z, ‖fderiv ℝ η z‖ ≤ Cη)
    {H H' : Space m → ℝ} (hH'1 : ContDiff ℝ 1 H') {MH MH' : ℝ} (hMH : ∀ y, |H' y| ≤ MH)
    (hMH' : ∀ y, ‖fderiv ℝ H' y‖ ≤ MH')
    (hH'ae : ∀ᵐ y, y ∈ ball (0 : Space m) (5 / 8) → H y = H' y)
    {C₅ s₂ : ℝ} (hC₅ : 0 < C₅)
    (hHA5 : ∀ w : Space (m + 1) → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
      tsupport w ⊆ ball 0 (5 / 4) → ∀ G : ℝ, (∀ y, ‖gradient w y‖ ≤ G) →
        (∫ y, ‖gradient (fun z ↦ zeroExtension g u (x₀ + R • Q z)) y‖ ^ 2 / R * w y ^ 2) ≤
          C₅ * (G / R) ^ 2 * (5 / 4) ^ m +
            C₅ * ∫ y in {y | zeroExtension g u (x₀ + R • Q y) < s₂},
              ‖gradient (fun z ↦ zeroExtension g u (x₀ + R • Q z)) y‖ ^ 2 / R * w y ^ 2)
    {δ'' τ s₁ : ℝ} (hδ''τ : δ'' ≤ τ) (hδ''58 : δ'' ≤ 5 / 8)
    (hthl : ∀ z ∈ closedBall (0 : Space (m + 1)) 2, z (Fin.last m) ≤ -δ'' →
      zeroExtension g u (x₀ + R • Q z) = 0)
    (hthu : ∀ z ∈ closedBall (0 : Space (m + 1)) 2, δ'' ≤ z (Fin.last m) →
      s₂ < zeroExtension g u (x₀ + R • Q z))
    {D : Set (Space m)} (hDo : IsOpen D) {ℓ ℓb r₀ b ρ : ℝ} (hρ : 9 / 16 < ρ) (hℓb : 0 < ℓb)
    (hℓbℓ : ℓb ≤ ℓ)
    (hgood : ∀ p, IsLayerGoodPoint R (fun z ↦ zeroExtension g u (x₀ + R • Q z))
      (verticalDirection m) ℓ r₀ b p → |p (Fin.last m)| < 1 → ‖horizontal p‖ < ρ →
        horizontal p ∈ D)
    (hbs₂ : s₂ ≤ 1 - b) {c : ℝ} {L : ℝ≥0} (hc : 0 < c) (hs : s₁ < s₂)
    {hh : ℝ → Space m → ℝ}
    (hG : LevelGraphFamily (fun z ↦ zeroExtension g u (x₀ + R • Q z)) D τ s₁ s₂ R c L hh)
    {σ : ℝ} (hσ : σ ∈ Icc s₁ s₂) {Λ Md T₁ : ℝ} (hΛ : 0 ≤ Λ) (hMd : 0 ≤ Md) (hT₁ : 0 ≤ T₁)
    (hlowband : ∀ p, horizontal p ∈ D → ‖horizontal p‖ < 9 / 16 → |p (Fin.last m)| < δ'' →
      0 < zeroExtension g u (x₀ + R • Q p) → zeroExtension g u (x₀ + R • Q p) < s₁ →
      (∀ r ∈ Ioc 0 (2 * r₀), ∫ z in ball p r, diffuseTiltDensity R
        (fun z ↦ zeroExtension g u (x₀ + R • Q z)) (verticalDirection m) z < ℓb * r ^ m) →
      |p (Fin.last m) - (hh s₁ (horizontal p) - T₁ / R)| ≤ Λ / R)
    (hdens : ∀ p, 0 < zeroExtension g u (x₀ + R • Q p) →
      ‖gradient (fun z ↦ zeroExtension g u (x₀ + R • Q z)) p‖ ^ 2 / R ≤ Md * R)
    (htiltA : ∫ z in closedBall (0 : Space (m + 1)) (19 / 16 + 2 * r₀),
      diffuseTiltDensity R (fun z ↦ zeroExtension g u (x₀ + R • Q z)) (verticalDirection m) z ≤
        2 ^ m * δ ^ 2) :
    (∫ z in tiltCylinder (verticalDirection m) (1 / 2),
      ((z (Fin.last m) - a) / δ - H (horizontal z)) ^ 2 *
        (R⁻¹ * ‖gradient (fun z ↦ zeroExtension g u (x₀ + R • Q z)) z‖ ^ 2)) ≤
      C₅ * (Cη * (5 / 8 + |a|) * (R * δ)⁻¹ + Cη * MH * R⁻¹ + (R * δ)⁻¹ + MH' * R⁻¹) ^ 2 *
          (5 / 4) ^ m +
        C₅ * (2 * (phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1)) * 5 ^ m /
              ℓb * 2 ^ m * (2 * (δ'' + |a|) ^ 2 + 2 * MH ^ 2 * δ ^ 2) +
          κ ^ 2 / c * (s₂ - s₁) * (2 * ((s₂ - s₁) / c * (R * δ)⁻¹) ^ 2 *
              volume.real (ball (0 : Space m) (9 / 16)) +
            2 * ∫ y in ball (0 : Space m) (9 / 16),
              (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H y) ^ 2) +
          2 * Λ * Md * ((2 * (Λ * (R * δ)⁻¹) ^ 2 +
              4 * ((s₂ - s₁) / c * (R * δ)⁻¹ + T₁ * (R * δ)⁻¹) ^ 2) *
              volume.real (ball (0 : Space m) (9 / 16)) +
            4 * ∫ y in ball (0 : Space m) (9 / 16),
              (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H y) ^ 2)) := by
  set L₀ := phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) with hL₀def
  have hL₀ : 0 ≤ L₀ := mul_nonneg (hr.phasePrimitive_one_pos h).le measureReal_nonneg
  have hvc : Continuous (fun z ↦ zeroExtension g u (x₀ + R • Q z)) :=
    h.zeroExtension_continuous.comp (continuous_const.add (Q.continuous.const_smul R))
  have hv0 : ∀ z, 0 ≤ zeroExtension g u (x₀ + R • Q z) := fun z ↦ h.zeroExtension_nonneg _
  have hgrad : ∀ z, ‖gradient (fun z ↦ zeroExtension g u (x₀ + R • Q z)) z‖ ≤ κ * R := by
    intro z
    have hLipv : LipschitzWith ⟨κ * R, mul_nonneg h.kappa_pos.le hR.le⟩
        (fun z ↦ zeroExtension g u (x₀ + R • Q z)) := by
      apply LipschitzWith.of_dist_le_mul
      intro p₁ p₂
      have := (hr.zeroExtension_lipschitzWith h).dist_le_mul (x₀ + R • Q p₁) (x₀ + R • Q p₂)
      rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hR.le, Q.dist_map] at this
      calc dist _ _ ≤ κ * (R * dist p₁ p₂) := this
        _ = κ * R * dist p₁ p₂ := by ring
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hLipv
  obtain ⟨hw1, hwcs, hwts, hwG⟩ :=
    heightMomentWeight_props hη1c hηcs hη1 hηtsl hCη hH'1 hMH hMH' a hδ
  have hint : Integrable (fun z ↦ ‖gradient (fun z ↦ zeroExtension g u (x₀ + R • Q z)) z‖ ^ 2 /
      R * (((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z) ^ 2) :=
    integrable_gradSq_div_mul_sq (h.locallyLipschitz_rescaled_translate x₀ R Q) R
      hw1.continuous hwcs
  have hHA5w := hHA5 _ hw1 hwcs (hwts.trans hηts) _ hwG
  -- the target is a part of the weighted mass
  have htarget : (∫ z in tiltCylinder (verticalDirection m) (1 / 2),
      ((z (Fin.last m) - a) / δ - H (horizontal z)) ^ 2 *
        (R⁻¹ * ‖gradient (fun z ↦ zeroExtension g u (x₀ + R • Q z)) z‖ ^ 2)) ≤
      ∫ z, ‖gradient (fun z ↦ zeroExtension g u (x₀ + R • Q z)) z‖ ^ 2 / R *
        (((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z) ^ 2 := by
    have hcongr : (∫ z in tiltCylinder (verticalDirection m) (1 / 2),
        ((z (Fin.last m) - a) / δ - H (horizontal z)) ^ 2 *
          (R⁻¹ * ‖gradient (fun z ↦ zeroExtension g u (x₀ + R • Q z)) z‖ ^ 2)) =
        ∫ z in tiltCylinder (verticalDirection m) (1 / 2),
          ‖gradient (fun z ↦ zeroExtension g u (x₀ + R • Q z)) z‖ ^ 2 / R *
            (((z (Fin.last m) - a) / δ - H' (horizontal z)) * η z) ^ 2 := by
      refine setIntegral_congr_ae (isOpen_tiltCylinder _ _).measurableSet ?_
      filter_upwards [ae_comp_horizontal hH'ae] with z hz hzQ
      have hzQ' := mem_tiltCylinder_vertical_iff.mp hzQ
      have hy : horizontal z ∈ ball (0 : Space m) (5 / 8) := by
        rw [mem_ball, dist_zero_right]
        linarith [hzQ'.1]
      rw [hz hy, hηQ z hzQ, mul_one]
      ring
    rw [hcongr]
    exact setIntegral_le_integral hint (Eventually.of_forall fun z ↦ by positivity)
  -- the thin layer
  have hthin : ∀ z, ‖horizontal z‖ < 9 / 16 → |z (Fin.last m)| < 5 / 8 →
      0 < zeroExtension g u (x₀ + R • Q z) → zeroExtension g u (x₀ + R • Q z) < s₂ →
      |z (Fin.last m)| < δ'' := by
    intro z h1 h2 h3 h4
    have hz2 : z ∈ closedBall (0 : Space (m + 1)) 2 := by
      rw [mem_closedBall, dist_zero_right]
      have := norm_le_norm_horizontal_add_abs_vertical z
      linarith
    rw [abs_lt]
    constructor
    · by_contra hn
      push Not at hn
      have := hthl z hz2 hn
      linarith
    · by_contra hn
      push Not at hn
      have := hthu z hz2 hn
      linarith
  -- the bad points
  have hbad := hr.rotated_kinetic_bad_set_le h hL₀ hsharp x₀ hR Q
    (isCompact_closedBall (0 : Space (m + 1)) (19 / 16 + 2 * r₀)) (2 * r₀) hℓb
  have h2L5 : 0 ≤ 2 * L₀ * 5 ^ m := by positivity
  have hCB : (ENNReal.ofReal (2 * L₀ * 5 ^ m) / ENNReal.ofReal ℓb) *
      ENNReal.ofReal (∫ p in closedBall (0 : Space (m + 1)) (19 / 16 + 2 * r₀),
        diffuseTiltDensity R (fun z ↦ zeroExtension g u (x₀ + R • Q z)) (verticalDirection m) p)
      ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.mpr hℓb).ne') ENNReal.ofReal_ne_top
  have hM := transitionHeightMoment_le hvc hv0 hR hδ hgrad hη1c.continuous hH'1.continuous
    (fun z ↦ rfl) hη1 hηsupp hMH hint hδ''τ hδ''58 hthin hDo hρ hℓbℓ hgood hbs₂ hc hs hG hσ hΛ hMd
    hT₁ hlowband hdens hCB hbad
  have htilt0 : 0 ≤ ∫ p in closedBall (0 : Space (m + 1)) (19 / 16 + 2 * r₀),
      diffuseTiltDensity R (fun z ↦ zeroExtension g u (x₀ + R • Q z)) (verticalDirection m) p :=
    setIntegral_nonneg measurableSet_closedBall fun p _ ↦
      diffuseTiltDensity_nonneg hR _ (norm_verticalDirection m) p
  have hCBle : ((ENNReal.ofReal (2 * L₀ * 5 ^ m) / ENNReal.ofReal ℓb) *
      ENNReal.ofReal (∫ p in closedBall (0 : Space (m + 1)) (19 / 16 + 2 * r₀),
        diffuseTiltDensity R (fun z ↦ zeroExtension g u (x₀ + R • Q z))
          (verticalDirection m) p)).toReal ≤ 2 * L₀ * 5 ^ m / ℓb * (2 ^ m * δ ^ 2) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofReal h2L5,
      ENNReal.toReal_ofReal hℓb.le, ENNReal.toReal_ofReal htilt0]
    exact mul_le_mul_of_nonneg_left htiltA (by positivity)
  -- the limit `H` in place of `H'`
  have hIeq : (∫ y in ball (0 : Space m) (9 / 16),
      (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H' y) ^ 2) =
      ∫ y in ball (0 : Space m) (9 / 16),
        (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H y) ^ 2 := by
    refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [hH'ae] with y hy hyb
    rw [hy (ball_subset_ball (by norm_num) hyb)]
  rw [hIeq] at hM
  set I := ∫ y in ball (0 : Space m) (9 / 16),
    (normalizedHeight (extendedHeight D L τ s₁ s₂ hh σ) a δ y - H y) ^ 2 with hIdef
  set V := volume.real (ball (0 : Space m) (9 / 16)) with hVdef
  have hWb0 : 0 ≤ 2 * (δ'' + |a|) ^ 2 / δ ^ 2 + 2 * MH ^ 2 := by positivity
  have hM' := hM.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hCBle hWb0) le_rfl) le_rfl)
  have hfinal := htarget.trans (hHA5w.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hM' hC₅.le)))
  refine hfinal.trans (le_of_eq ?_)
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hR0 : R ≠ 0 := hR.ne'
  have hWbδ : (2 * (δ'' + |a|) ^ 2 / δ ^ 2 + 2 * MH ^ 2) * (2 * L₀ * 5 ^ m / ℓb *
      (2 ^ m * δ ^ 2)) =
        2 * L₀ * 5 ^ m / ℓb * 2 ^ m * (2 * (δ'' + |a|) ^ 2 + 2 * MH ^ 2 * δ ^ 2) := by
    field_simp
  rw [hWbδ]
  ring

/-! ### HA6.1 along aligned sequences -/

/-- **HA6.1 (weighted height approximation), with a regular representative of the limit.**
There are thresholds `b₅, σ₀ > 0` (depending only on `g, u, f`) such that for all layer
parameters with `0 < ℓ`, `0 < r₀ < 13/32`, `0 < b ≤ 1 - s₂`, `9/16 < ρ`, `0 < τ ≤ 1`,
`0 < s₁ < σ₀`, `s₁ < s₂ < 1`, `2 (1 - s₂) ≤ b₅` and `0 < c`: along an aligned sequence with
height-limit data whose centers tend to `0` and whose limit `H` agrees a.e. on `B_{5/8}` with a
compactly supported `C¹` function,
`∫_{Q_{1/2}} ((t - a_j)/δ_j - H(y))² ε |∇v_j|² → 0`. -/
theorem RigidityHypotheses.tendsto_alignedHeightMoment_of_regular
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    ∃ b₅ σ₀ : ℝ, 0 < b₅ ∧ 0 < σ₀ ∧
      ∀ (ℓ r₀ b ρ τ s₁ s₂ c K : ℝ) (L : ℝ≥0), 0 < ℓ → 0 < r₀ → r₀ < 13 / 32 → 0 < b →
        b ≤ 1 - s₂ → 9 / 16 < ρ → 0 < τ → τ ≤ 1 → 0 < s₁ → s₁ < σ₀ → s₁ < s₂ → s₂ < 1 →
        2 * (1 - s₂) ≤ b₅ → 0 < c →
      ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
        (δ : ℕ → ℝ) (e : Space (m + 1)), IsAlignedSequence g u x R Q δ e →
      ∀ (φ : ℕ → ℕ) (σl a : ℕ → ℝ) (H : Space m → ℝ),
        IsAlignedHeightLimit g u ℓ r₀ b ρ τ s₁ s₂ L c K x R Q δ φ σl a H →
        Tendsto a atTop (𝓝 0) →
        (∃ H' : Space m → ℝ, ContDiff ℝ 1 H' ∧ HasCompactSupport H' ∧
          ∀ᵐ y, y ∈ ball (0 : Space m) (5 / 8) → H y = H' y) →
        Tendsto (fun j ↦ ∫ z in tiltCylinder (verticalDirection m) (1 / 2),
          ((z (Fin.last m) - a j) / δ (φ j) - H (horizontal z)) ^ 2 *
            ((R (φ j))⁻¹ * ‖gradient (fun z ↦ zeroExtension g u
              (x (φ j) + R (φ j) • Q (φ j) z)) z‖ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨b₅, C₅, hb₅, -, hC₅, hHA5⟩ :=
    hr.exists_stable_well_height_bounds_of_sharp_energy h hsharp
  obtain ⟨α₁, hα₁, hHA10⟩ := hr.exists_low_profile_approximation_of_le h hsharp
  obtain ⟨Kb, αb, hKb, hαb, hband⟩ := hr.exists_low_band_localization h
  obtain ⟨cq, sq, hcq, hsq, hqlin⟩ := hr.exists_layerProfile_linear_lower h
  obtain ⟨Md, hMd, hdens⟩ := hr.exists_rotated_rescaled_density_bound h
  refine ⟨b₅, min α₁ (cq * sq / 2), hb₅, lt_min hα₁ (by positivity), ?_⟩
  intro ℓ r₀ b ρ τ s₁ s₂ c K L hℓ hr₀ hr₀' hb hbs₂ hρ hτ hτ1 hs₁ hs₁σ hs₁₂ hs₂ hb₅s hc
    x R Q δ e hal φ σl a H hlim ha hreg
  obtain ⟨-, hR, hRt, hδ, hδ0, hRδ, htilt, he, hloc, hQ⟩ := hal
  obtain ⟨hφ, hσ, -, hHA9, -, -, -, hconv⟩ := hlim
  obtain ⟨H', hH'1, hH'c, hH'ae⟩ := hreg
  -- constants
  have hs₁α₁ : s₁ < α₁ := hs₁σ.trans_le (min_le_left _ _)
  have hs₁q : s₁ < cq * sq / 2 := hs₁σ.trans_le (min_le_right _ _)
  have hb1 : b < 1 := by linarith
  have hs₁b : s₁ < 1 - b := by linarith
  set α := min αb ((cq * sq - s₁) / 2) with hαdef
  have hα0 : 0 < α := lt_min hαb (by linarith)
  have hααb : α ≤ αb := min_le_left _ _
  have hs₁α : s₁ + α < cq * sq := by
    have : α ≤ (cq * sq - s₁) / 2 := min_le_right _ _
    linarith
  set Λ := Kb * α + (s₁ + α) / cq with hΛdef
  have hΛ0 : 0 ≤ Λ := by positivity
  obtain ⟨ℓ₁₀, ρ₀, Cw, hℓ₁₀, -, hCw, hHA10'⟩ :=
    hHA10 Kb α hKb hα0 b ⟨hb, hb1⟩ s₁ ⟨hs₁, hs₁α₁⟩ hs₁b L
  have hℓ₁ : 0 < min ℓ ℓ₁₀ := lt_min hℓ hℓ₁₀
  obtain ⟨ℓ', hℓ', happrox⟩ := hHA10' (min ℓ ℓ₁₀) hℓ₁ (min_le_right _ _)
  set ℓb := min (min ℓ ℓ₁₀) ℓ' with hℓbdef
  have hℓb : 0 < ℓb := lt_min hℓ₁ hℓ'
  have hℓbℓ : ℓb ≤ ℓ := (min_le_left _ _).trans (min_le_left _ _)
  have hℓbℓ' : ℓb ≤ ℓ' := min_le_right _ _
  have hT₁0 : 0 ≤ layerTravelTime f s₁ := (hr.layerTravelTime_pos h ⟨hs₁, by linarith⟩).le
  have hL₀ : 0 ≤ phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) :=
    mul_nonneg (hr.phasePrimitive_one_pos h).le measureReal_nonneg
  -- the cutoff and the regular limit
  obtain ⟨η, hη1c, hηcs, hη1, hηQ, hηsupp, hηts, hηtsl, Cη, hCη⟩ :=
    exists_heightMomentCutoff (m := m)
  obtain ⟨MH, hMH⟩ := hH'1.continuous.bounded_above_of_compact_support hH'c
  obtain ⟨MH', hMH'⟩ := (hH'1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hH'c.fderiv (𝕜 := ℝ))
  have hMH0 : 0 ≤ MH := (norm_nonneg _).trans (hMH 0)
  have hMH'0 : 0 ≤ MH' := (norm_nonneg _).trans (hMH' 0)
  have hCη0 : 0 ≤ Cη := (norm_nonneg _).trans (hCη 0)
  have hMHa : ∀ y, |H' y| ≤ MH := fun y ↦ by rw [← Real.norm_eq_abs]; exact hMH y
  -- the subsequence
  set v : ℕ → Space (m + 1) → ℝ := fun j z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)
    with hvdef
  have hRφ : ∀ j, 0 < R (φ j) := fun j ↦ hR (φ j)
  have hRφt : Tendsto (fun j ↦ R (φ j)) atTop atTop := hRt.comp hφ.tendsto_atTop
  have hδφ : ∀ j, 0 < δ (φ j) := fun j ↦ hδ (φ j)
  have hδφ0 : Tendsto (fun j ↦ δ (φ j)) atTop (𝓝 0) := hδ0.comp hφ.tendsto_atTop
  have hRδφ : Tendsto (fun j ↦ R (φ j) * δ (φ j)) atTop atTop := hRδ.comp hφ.tendsto_atTop
  have hQφ : Tendsto (fun j ↦ Q (φ j) (verticalDirection m)) atTop (𝓝 e) :=
    hQ.comp hφ.tendsto_atTop
  have hlocφ : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x (φ j) + R (φ j) • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0) :=
    fun K hK ↦ (hloc K hK).comp hφ.tendsto_atTop
  have hV : VerticalPlanarLayers v :=
    hr.verticalPlanarLayers_of_rotated h hsharp (fun j ↦ x (φ j)) hRφ hRφt he hlocφ hQφ
  have hdiff : ∀ j z, 0 < v j z → DifferentiableAt ℝ (v j) z := fun j z hz ↦
    h.differentiableAt_rescaled_of_pos (x (φ j)) (R (φ j)) (Q (φ j)) hz
  set D : ℕ → Set (Space m) := fun j ↦ verticalGoodSet (R (φ j)) (v j) ℓ r₀ b ρ with hDdef
  have hevLGF : ∀ᶠ j in atTop, LevelGraphFamily (v j) (D j) τ s₁ s₂ (R (φ j)) c L
      (fun s y ↦ slabLevelHeight (v j) τ s y) := by
    filter_upwards [hHA9, hV.eventually_hasLevelSlope_of_cone hdiff (ρ := ρ) (c := c) hτ hs₁ hs₂
      hRφ L, hV.eventually_levelGraphFamily hdiff ρ (c := c) hτ hs₁ hs₂ (fun j ↦ R (φ j)) L]
      with j hj h1 h2
    have hDsub : D j ⊆ closedBall (0 : Space m) ρ := fun y hy ↦ ball_subset_closedBall hy.2
    exact h2 (D j) hDsub hj.1 (h1 (D j) hDsub hj.1 hj.2)
  have hevR : ∀ᶠ j in atTop, ρ₀ ≤ R (φ j) * r₀ ∧ Cw ≤ R (φ j) * r₀ ∧
      τ / 2 + Cw / R (φ j) < τ ∧ 9 / 16 + Cw / R (φ j) < ρ := by
    have hμ : 0 < min (τ / 2) (ρ - 9 / 16) := lt_min (by positivity) (by linarith)
    filter_upwards [hRφt.eventually_ge_atTop (max (ρ₀ / r₀) (max (Cw / r₀)
      (2 * Cw / min (τ / 2) (ρ - 9 / 16) + 1)))] with j hj
    have hRj := hRφ j
    have h1 : ρ₀ / r₀ ≤ R (φ j) := (le_max_left _ _).trans hj
    have h2 : Cw / r₀ ≤ R (φ j) := (le_max_left _ _).trans ((le_max_right _ _).trans hj)
    have h3 : 2 * Cw / min (τ / 2) (ρ - 9 / 16) + 1 ≤ R (φ j) :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hj)
    have h3' : Cw / R (φ j) < min (τ / 2) (ρ - 9 / 16) := by
      rw [div_lt_iff₀ hRj]
      have h4 : 2 * Cw / min (τ / 2) (ρ - 9 / 16) < R (φ j) := by linarith
      rw [div_lt_iff₀ hμ] at h4
      have h5 := mul_comm (R (φ j)) (min (τ / 2) (ρ - 9 / 16))
      linarith
    refine ⟨by rwa [div_le_iff₀ hr₀] at h1, by rwa [div_le_iff₀ hr₀] at h2, ?_, ?_⟩
    · linarith [min_le_left (τ / 2) (ρ - 9 / 16)]
    · linarith [min_le_right (τ / 2) (ρ - 9 / 16)]
  have hevlow := hV.lower (ρ + τ) (τ / 2) (by positivity)
  have hevhigh := hV.upper (ρ + τ) (τ / 2) b (by positivity) hb
  -- the tilt in the cylinder `Q_2`
  have hQ2 : closedBall (0 : Space (m + 1)) (19 / 16 + 2 * r₀) ⊆
      tiltCylinder (verticalDirection m) 2 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_tiltCylinder_vertical_iff]
    have h1 : ‖horizontal z‖ ≤ ‖z‖ := by
      have := lipschitzWith_one_horizontal.dist_le_mul z 0
      have h0 : horizontal (0 : Space (m + 1)) = 0 := by
        rw [← horizontalContinuousLinearMap_apply', map_zero]
      rwa [NNReal.coe_one, one_mul, dist_zero_right, h0, dist_zero_right] at this
    have h2 : |z (Fin.last m)| ≤ ‖z‖ := by
      have := abs_last_sub_le_norm_ahm z 0
      simpa using this
    constructor <;> linarith
  have htiltA : ∀ j, ∫ z in closedBall (0 : Space (m + 1)) (19 / 16 + 2 * r₀),
      diffuseTiltDensity (R (φ j)) (v j) (verticalDirection m) z ≤ 2 ^ m * δ (φ j) ^ 2 := by
    intro j
    have hvL : LocallyLipschitz (v j) := h.locallyLipschitz_rescaled_translate _ _ _
    have hQ2b : tiltCylinder (verticalDirection m) 2 ⊆ closedBall (0 : Space (m + 1)) 4 := by
      intro z hz
      rw [mem_tiltCylinder_vertical_iff] at hz
      have := norm_le_norm_horizontal_add_abs_vertical z
      rw [mem_closedBall, dist_zero_right]
      linarith [hz.1, hz.2]
    have hint : IntegrableOn (diffuseTiltDensity (R (φ j)) (v j) (verticalDirection m))
        (tiltCylinder (verticalDirection m) 2) :=
      (integrableOn_diffuseTiltDensity hvL (isCompact_closedBall _ _) (R (φ j))
        (norm_verticalDirection m)).mono_set hQ2b
    have hT := htilt (φ j)
    rw [cylinderTilt, zpow_neg, zpow_natCast] at hT
    have hT' : ∫ z in tiltCylinder (verticalDirection m) 2,
        diffuseTiltDensity (R (φ j)) (v j) (verticalDirection m) z = 2 ^ m * δ (φ j) ^ 2 := by
      have h2m : (0 : ℝ) < 2 ^ m := by positivity
      field_simp at hT
      linarith
    rw [← hT']
    exact setIntegral_mono_set hint (ae_of_all _ fun z ↦
      diffuseTiltDensity_nonneg (hRφ j) _ (norm_verticalDirection m) z) (Eventually.of_forall hQ2)
  -- the bound sequences
  set V := volume.real (ball (0 : Space m) (9 / 16)) with hVdef
  set Iseq : ℕ → ℝ := fun j ↦ ∫ y in ball (0 : Space m) (9 / 16),
    (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j) y - H y) ^ 2
    with hIseqdef
  have hI : Tendsto Iseq atTop (𝓝 0) := hconv (9 / 16) hρ
  set Kb' := 2 * (phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1)) * 5 ^ m / ℓb *
    2 ^ m with hKb'def
  have hKb'0 : 0 ≤ Kb' := by positivity
  set Pseq : ℕ → ℝ := fun j ↦ (R (φ j) * δ (φ j))⁻¹ with hPdef
  set Qseq : ℕ → ℝ := fun j ↦ (R (φ j))⁻¹ with hQdef
  set Φ : ℝ → ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun δ'' p ↦
    C₅ * (Cη * (5 / 8 + p.2.2.1) * p.1 + Cη * MH * p.2.1 + p.1 + MH' * p.2.1) ^ 2 *
        (5 / 4) ^ m +
      C₅ * (Kb' * (2 * (δ'' + p.2.2.1) ^ 2 + 2 * MH ^ 2 * p.2.2.2.1 ^ 2) +
        κ ^ 2 / c * (s₂ - s₁) * (2 * ((s₂ - s₁) / c * p.1) ^ 2 * V + 2 * p.2.2.2.2) +
        2 * Λ * Md * ((2 * (Λ * p.1) ^ 2 +
          4 * ((s₂ - s₁) / c * p.1 + layerTravelTime f s₁ * p.1) ^ 2) * V +
          4 * p.2.2.2.2)) with hΦdef
  set seq : ℕ → ℝ × ℝ × ℝ × ℝ × ℝ := fun j ↦
    (Pseq j, Qseq j, |a j|, δ (φ j), Iseq j) with hseqdef
  have hseq : Tendsto seq atTop (𝓝 (0, 0, 0, 0, 0)) := by
    have hP : Tendsto Pseq atTop (𝓝 0) := hRδφ.inv_tendsto_atTop
    have hQs : Tendsto Qseq atTop (𝓝 0) := hRφt.inv_tendsto_atTop
    have hA : Tendsto (fun j ↦ |a j|) atTop (𝓝 0) := by
      have h0 := (continuous_abs.tendsto (0 : ℝ)).comp ha
      rw [abs_zero] at h0
      exact h0
    exact hP.prodMk_nhds (hQs.prodMk_nhds (hA.prodMk_nhds (hδφ0.prodMk_nhds hI)))
  have hUlim : ∀ δ'' : ℝ, Tendsto (fun j ↦ Φ δ'' (seq j)) atTop
      (𝓝 (C₅ * (Kb' * (2 * δ'' ^ 2)))) := by
    intro δ''
    have hΦc : Continuous (Φ δ'') := by
      simp only [hΦdef]
      fun_prop
    have hlim := (hΦc.tendsto _).comp hseq
    have hΦ0 : Φ δ'' (0, 0, 0, 0, 0) = C₅ * (Kb' * (2 * δ'' ^ 2)) := by
      simp only [hΦdef]
      ring
    rw [hΦ0] at hlim
    exact hlim
  -- the integrands are nonnegative
  have htarget0 : ∀ j, 0 ≤ ∫ z in tiltCylinder (verticalDirection m) (1 / 2),
      ((z (Fin.last m) - a j) / δ (φ j) - H (horizontal z)) ^ 2 *
        ((R (φ j))⁻¹ * ‖gradient (fun z ↦ zeroExtension g u
          (x (φ j) + R (φ j) • Q (φ j) z)) z‖ ^ 2) := fun j ↦
    setIntegral_nonneg (isOpen_tiltCylinder _ _).measurableSet fun z _ ↦
      mul_nonneg (sq_nonneg _) (mul_nonneg (inv_nonneg.mpr (hRφ j).le) (sq_nonneg _))
  -- the bound at each scale
  have hU : ∀ δ'' : ℝ, 0 < δ'' → δ'' ≤ min τ (5 / 8) → ∀ᶠ j in atTop,
      (∫ z in tiltCylinder (verticalDirection m) (1 / 2),
        ((z (Fin.last m) - a j) / δ (φ j) - H (horizontal z)) ^ 2 *
          ((R (φ j))⁻¹ * ‖gradient (fun z ↦ zeroExtension g u
            (x (φ j) + R (φ j) • Q (φ j) z)) z‖ ^ 2)) ≤ Φ δ'' (seq j) := by
    intro δ'' hδ''0 hδ''le
    have hδ''τ : δ'' ≤ τ := hδ''le.trans (min_le_left _ _)
    have hδ''58 : δ'' ≤ 5 / 8 := hδ''le.trans (min_le_right _ _)
    filter_upwards [hevLGF, hevR, hevlow, hevhigh, hV.lower 2 δ'' hδ''0,
      hV.upper 2 δ'' (1 - s₂) hδ''0 (by linarith), hHA9] with j hLGF hRj hlowj hhighj hthl hthu
      hHA9j
    have hRj0 := hRφ j
    have hvL := hr.lipschitzWith_rescaled h (x (φ j)) hRj0.le (Q (φ j))
    have hDo : IsOpen (D j) := isOpen_verticalGoodSet hRj0 hvL ℓ r₀ b ρ
    have hcone₁ : HasLevelCone (v j) (D j) τ s₁ s₁ L := hHA9j.1.of_mem_Icc ⟨le_rfl, hs₁₂.le⟩
    have hfull : ∀ A, IsLayerGoodPoint (R (φ j)) (v j) (verticalDirection m) (min ℓ ℓ₁₀) r₀ b A →
        |A (Fin.last m)| < τ → ‖horizontal A‖ < ρ → horizontal A ∈ D j := by
      intro A hA hAτ hAρ
      exact horizontal_mem_verticalGoodSet ⟨hA.1, fun r hr ↦ (hA.2 r hr).trans_le
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hr.1.le m))⟩
        (hAτ.trans_le hτ1) hAρ
    have hmemB : ∀ y ∈ D j, ∀ t ∈ Ioo (-τ) τ,
        point y t ∈ closedBall (0 : Space (m + 1)) (ρ + τ) := by
      intro y hy t ht
      rw [mem_closedBall, dist_zero_right]
      have h1 := norm_point_le y t
      have h2 : ‖y‖ < ρ := by
        have := hy.2
        rwa [mem_ball, dist_zero_right] at this
      have h3 : |t| < τ := abs_lt.mpr ht
      linarith
    have hlowHA10 : ∀ y ∈ D j, ∀ t ∈ Ioo (-τ) τ, t ≤ -(τ / 2) →
        zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) (point y t)) = 0 := fun y hy t ht htle ↦
      hlowj (point y t) (hmemB y hy t ht) (by rw [last_point]; exact htle)
    have hhighHA10 : ∀ y ∈ D j, ∀ t ∈ Ioo (-τ) τ, τ / 2 ≤ t →
        1 - b < zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) (point y t)) :=
      fun y hy t ht htle ↦ hhighj (point y t) (hmemB y hy t ht) (by rw [last_point]; exact htle)
    have hlowband : ∀ p, horizontal p ∈ D j → ‖horizontal p‖ < 9 / 16 →
        |p (Fin.last m)| < δ'' → 0 < v j p → v j p < s₁ →
        (∀ r ∈ Ioc 0 (2 * r₀), ∫ z in ball p r, diffuseTiltDensity (R (φ j)) (v j)
          (verticalDirection m) z < ℓb * r ^ m) →
        |p (Fin.last m) - (slabLevelHeight (v j) τ s₁ (horizontal p) -
          layerTravelTime f s₁ / R (φ j))| ≤ Λ / R (φ j) := by
      intro p hpD hp916 hpn hpos hplow hpgood
      have hpt : point (horizontal p) (p (Fin.last m)) = p := point_horizontal_last p
      have htmem : p (Fin.last m) ∈ Ioo (-τ) τ := by
        rw [abs_lt] at hpn
        exact ⟨by linarith, by linarith⟩
      have hyρ : ‖horizontal p‖ + Cw / R (φ j) < ρ := by linarith [hRj.2.2.2]
      have hdich := happrox (x (φ j)) (R (φ j)) hRj0 (Q (φ j)) (D j) r₀ τ (τ / 2) b ρ s₁ hRj.1
        hRj.2.1 (by positivity) hRj.2.2.1 le_rfl hs₁b le_rfl hcone₁ hfull hlowHA10 hhighHA10
        (horizontal p) hpD hyρ (p (Fin.last m)) htmem (by rw [hpt]; exact hpos)
        (by rw [hpt]; exact hplow)
      rw [hpt] at hdich
      rcases hdich with ⟨r, hr, hrbad⟩ | happ
      · exfalso
        have h1 : ∫ z in ball p r, diffuseTiltDensity (R (φ j)) (v j) (verticalDirection m) z <
            ℓ' * r ^ m := (hpgood r hr).trans_le
          (mul_le_mul_of_nonneg_right hℓbℓ' (pow_nonneg hr.1.le m))
        exact (lt_irrefl _) (hrbad.trans_lt h1)
      · have hb := hband (x (φ j)) (R (φ j)) hRj0 (Q (φ j)) (layerProfile f)
          (fun s hs ↦ layerProfile_of_nonpos f hs) cq sq hcq hqlin _ α s₁ hα0 hααb hs₁α p happ
          hpos hplow
        exact abs_sub_le_div_of_band hRj0 (by positivity) (by positivity) hb.1 hb.2
    exact hr.heightMoment_le_of_scale h hsharp hRj0 (hδφ j) hη1c hηcs hη1 hηQ hηsupp hηts hηtsl
      hCη hH'1 hMHa hMH' hH'ae hC₅
      (fun w hw hwc hwr G hG ↦ by
        have := (hHA5 (x (φ j)) (R (φ j)) hRj0 (Q (φ j)) (1 - s₂) (by linarith) hb₅s 1 one_pos
          (5 / 4) (by norm_num) w hw hwc hwr G hG).1
        simpa only [sub_sub_cancel] using this)
      hδ''τ hδ''58 hthl (fun z hz hzn ↦ by
        have := hthu z hz hzn
        rwa [sub_sub_cancel] at this) hDo hρ hℓb hℓbℓ
      (fun p hp hp1 hpρ ↦ horizontal_mem_verticalGoodSet hp hp1 hpρ) (by linarith) hc hs₁₂ hLGF
      (hσ j)
      hΛ0 hMd hT₁0 hlowband (fun p hp ↦ hdens (x (φ j)) (R (φ j)) hRj0 (Q (φ j)) p hp)
      (htiltA j)
  -- conclusion
  rw [tendsto_order]
  refine ⟨fun ε hε ↦ Eventually.of_forall fun j ↦ hε.trans_le (htarget0 j), fun ε hε ↦ ?_⟩
  set Kδ := C₅ * Kb' * 2 + 1 with hKδdef
  have hKδ : 0 < Kδ := by positivity
  set δ'' := min (min τ (5 / 8)) (ε / Kδ) with hδ''def
  have hδ''0 : 0 < δ'' := lt_min (lt_min hτ (by norm_num)) (div_pos hε hKδ)
  have hδ''le : δ'' ≤ min τ (5 / 8) := min_le_left _ _
  have hsmall : C₅ * (Kb' * (2 * δ'' ^ 2)) < ε := by
    have h1 : δ'' ≤ ε / Kδ := min_le_right _ _
    have h2 : δ'' ≤ 1 := hδ''le.trans ((min_le_right _ _).trans (by norm_num))
    have h3 : δ'' ^ 2 ≤ δ'' := pow_le_of_le_one hδ''0.le h2 two_ne_zero
    have h4 : δ'' * Kδ ≤ ε := by rwa [le_div_iff₀ hKδ] at h1
    have h6 : 0 ≤ C₅ * Kb' * 2 := by positivity
    have h5 : C₅ * (Kb' * (2 * δ'' ^ 2)) ≤ (C₅ * Kb' * 2) * δ'' := by
      calc C₅ * (Kb' * (2 * δ'' ^ 2)) = (C₅ * Kb' * 2) * δ'' ^ 2 := by ring
        _ ≤ (C₅ * Kb' * 2) * δ'' := mul_le_mul_of_nonneg_left h3 h6
    have h7 : (C₅ * Kb' * 2) * δ'' < Kδ * δ'' := by
      apply mul_lt_mul_of_pos_right _ hδ''0
      rw [hKδdef]
      linarith
    have h8 : Kδ * δ'' = δ'' * Kδ := mul_comm _ _
    linarith
  filter_upwards [hU δ'' hδ''0 hδ''le, (hUlim δ'').eventually (gt_mem_nhds hsmall)]
    with j h1 h2
  exact h1.trans_lt h2

/-! ### The regular representative of the limit and HA6.1 -/

/-- **The limit height has a regular representative (from the flux identification).** If the
flux identification (C) holds, then along an aligned sequence with height-limit data the `L²`
limit `H` agrees a.e. on `B_{5/8}` with a compactly supported `C¹` function (the weak Dirichlet
pairings vanish, so `H` is weakly harmonic on `B_{3/4}` and smooth by Weyl's lemma). -/
theorem RigidityHypotheses.exists_regular_alignedHeightLimit (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {ℓ r₀ b ρ τ s₁ s₂ c K : ℝ} {L : ℝ≥0} (hρ : 3 / 4 < ρ)
    (hC : HasAlignedFluxIdentification g u (phasePrimitive f 1) ℓ r₀ b ρ τ s₁ s₂ L c K)
    {x : ℕ → Space (m + 1)} {R : ℕ → ℝ} {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    {δ : ℕ → ℝ} {e : Space (m + 1)} (hal : IsAlignedSequence g u x R Q δ e)
    {φ : ℕ → ℕ} {σl a : ℕ → ℝ} {H : Space m → ℝ}
    (hlim : IsAlignedHeightLimit g u ℓ r₀ b ρ τ s₁ s₂ L c K x R Q δ φ σl a H) :
    ∃ H' : Space m → ℝ, ContDiff ℝ 1 H' ∧ HasCompactSupport H' ∧
      ∀ᵐ y, y ∈ ball (0 : Space m) (5 / 8) → H y = H' y := by
  have hCC := hC x R Q δ e hal φ σl a H hlim
  obtain ⟨-, hR, hRt, hδ, hδ0, hRδ, -, he, hloc, hQ⟩ := hal
  obtain ⟨hφ, -, -, -, hLip, -, hHL2, hconv⟩ := hlim
  set fj : ℕ → Space m → ℝ := fun j ↦
    alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j) with hfj
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
  have hψs1 : tsupport (⇑bψ) ⊆ Ioo (-1) 1 :=
    hψs.trans (Ioo_subset_Ioo (by norm_num) (by norm_num))
  -- step 1: the Dirichlet pairings of the heights vanish
  have hweak : ∀ ψs : Space m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψs → HasCompactSupport ψs →
      tsupport ψs ⊆ ball (0 : Space m) (3 / 4) →
        Tendsto (fun j ↦ ∫ y, inner ℝ (gradient (fj j) y) (gradient ψs y)) atTop (𝓝 0) := by
    intro ψs hψsm hcψs hsubs
    have hψs1' : ContDiff ℝ 1 ψs := hψsm.of_le (by norm_num)
    have hgs : tsupport (gradient ψs) ⊆ ball (0 : Space m) (3 / 4) := by
      refine (closure_minimal (fun y hy ↦ ?_) (isClosed_tsupport ψs)).trans hsubs
      by_contra hn
      exact hy (ha6_gradient_eq_zero_of_notMem_tsupport hn)
    have h1 := hCC (gradient ψs) (ha6_continuous_gradient hψs1') hgs (⇑bψ) bψ.continuous hψs
    have h2 := (hr.tendsto_flux_gradient_of_aligned h hsharp x hR hRt hδ hδ0 hRδ he hloc hQ
      hψs1' hcψs (hsubs.trans (ball_subset_ball (by norm_num))) bψ.contDiff
      bψ.hasCompactSupport hψs1 (c₀ := 1 / 4) (by norm_num) hdψ).comp hφ.tendsto_atTop
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    have h4 : Tendsto (fun j ↦ phasePrimitive f 1 *
        ∫ y, inner ℝ (gradient ψs y) (gradient (fj j) y)) atTop (𝓝 0) := by
      refine h3.congr fun j ↦ ?_
      simp only [Function.comp, hψ0, mul_one, hfj]
      ring
    have h5 := h4.const_mul (phasePrimitive f 1)⁻¹
    rw [mul_zero] at h5
    refine h5.congr fun j ↦ ?_
    rw [← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul]
    exact integral_congr_ae (Eventually.of_forall fun y ↦ real_inner_comm _ _)
  -- step 2: the limit is weakly harmonic, hence smooth (Weyl)
  have hvw : IsVeryWeaklyHarmonicOn (ball (0 : Space m) (3 / 4)) H :=
    weakHarmonic_of_sq_tendsto (x := (0 : Space m)) (R := 3 / 4) (f := fj) (fun j ↦ hLip j)
      (fun r hr' ↦ hHL2 r (hr'.trans hρ)) (fun r hr' ↦ hconv r (hr'.trans hρ)) hweak
  obtain ⟨H', hH'c, hΔ', hae⟩ := weyl_lemma isOpen_ball hvw
  have haeB : ∀ᵐ y, y ∈ ball (0 : Space m) (3 / 4) → H y = H' y :=
    (ae_restrict_iff' measurableSet_ball).mp hae
  let bκ : ContDiffBump (0 : Space m) := ⟨5 / 8, 11 / 16, by norm_num, by norm_num⟩
  have htsκ : tsupport (⇑bκ) = closedBall 0 (11 / 16) := bκ.tsupport_eq
  refine ⟨fun y ↦ bκ y * H' y, ?_, bκ.hasCompactSupport.mul_right, ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun y ↦ ?_
    by_cases hy : y ∈ ball (0 : Space m) (3 / 4)
    · exact (bκ.contDiff.contDiffAt).mul
        ((hH'c.contDiffAt (isOpen_ball.mem_nhds hy)).of_le (by norm_num))
    · have hyt : y ∉ tsupport (⇑bκ) := by
        rw [htsκ, mem_closedBall, dist_zero_right]
        intro hle
        apply hy
        rw [mem_ball, dist_zero_right]
        linarith
      have hev : (fun y ↦ bκ y * H' y) =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport (⇑bκ)).isOpen_compl.mem_nhds hyt] with z hz
        simp [image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · filter_upwards [haeB] with y hy hyb
    have h1 : bκ y = 1 := bκ.one_of_mem_closedBall (ball_subset_closedBall hyb)
    rw [hy (ball_subset_ball (by norm_num) hyb), h1, one_mul]

/-- **(B2) HA6.1 for aligned height-limit data.** Under the same parameter conditions as
`RigidityHypotheses.tendsto_alignedHeightMoment_of_regular`, together with `3/4 < ρ`,
`ρ + r₀ < 2` and the flux identification (C) for the same parameters, the weighted height
approximation `∫_{Q_{1/2}} ((t - a_j)/δ_j - H(y))² ε |∇v_j|² → 0` holds along every aligned
sequence with height-limit data. -/
theorem RigidityHypotheses.tendsto_alignedHeightMoment (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    ∃ b₅ σ₀ : ℝ, 0 < b₅ ∧ 0 < σ₀ ∧
      ∀ (ℓ r₀ b ρ τ s₁ s₂ c K : ℝ) (L : ℝ≥0), 0 < ℓ → 0 < r₀ → r₀ < 13 / 32 → 0 < b →
        b ≤ 1 - s₂ → 3 / 4 < ρ → ρ + r₀ < 2 → 0 < τ → τ ≤ 1 → 0 < s₁ → s₁ < σ₀ →
        s₁ < s₂ → s₂ < 1 → 2 * (1 - s₂) ≤ b₅ → 0 < c →
        HasAlignedFluxIdentification g u (phasePrimitive f 1) ℓ r₀ b ρ τ s₁ s₂ L c K →
      ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
        (δ : ℕ → ℝ) (e : Space (m + 1)), IsAlignedSequence g u x R Q δ e →
      ∀ (φ : ℕ → ℕ) (σl a : ℕ → ℝ) (H : Space m → ℝ),
        IsAlignedHeightLimit g u ℓ r₀ b ρ τ s₁ s₂ L c K x R Q δ φ σl a H →
        Tendsto (fun j ↦ ∫ z in tiltCylinder (verticalDirection m) (1 / 2),
          ((z (Fin.last m) - a j) / δ (φ j) - H (horizontal z)) ^ 2 *
            ((R (φ j))⁻¹ * ‖gradient (fun z ↦ zeroExtension g u
              (x (φ j) + R (φ j) • Q (φ j) z)) z‖ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨b₅, σ₀, hb₅, hσ₀, hmain⟩ := hr.tendsto_alignedHeightMoment_of_regular h hsharp
  refine ⟨b₅, σ₀, hb₅, hσ₀, ?_⟩
  intro ℓ r₀ b ρ τ s₁ s₂ c K L hℓ hr₀ hr₀' hb hbs₂ hρ hρr₀ hτ hτ1 hs₁ hs₁σ hs₁₂ hs₂ hb₅s hc
    hC x R Q δ e hal φ σl a H hlim
  have ha : Tendsto a atTop (𝓝 0) :=
    hr.tendsto_alignedCenter_zero h hsharp hℓ hb.le (by linarith) (by linarith) hτ hs₁ hs₂
      (by rw [abs_of_pos hr₀]; exact hρr₀) hal hlim
  exact hmain ℓ r₀ b ρ τ s₁ s₂ c K L hℓ hr₀ hr₀' hb hbs₂ (by linarith) hτ hτ1 hs₁ hs₁σ hs₁₂
    hs₂ hb₅s hc x R Q δ e hal φ σl a H hlim ha
    (hr.exists_regular_alignedHeightLimit h hsharp hρ hC hal hlim)

/-- **(B) `HasAlignedHeightMoments` from the flux identification (C).** -/
theorem RigidityHypotheses.hasAlignedHeightMoments_of_fluxIdentification
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    ∃ b₅ σ₀ : ℝ, 0 < b₅ ∧ 0 < σ₀ ∧
      ∀ (ℓ r₀ b ρ τ s₁ s₂ c K : ℝ) (L : ℝ≥0), 0 < ℓ → 0 < r₀ → r₀ < 13 / 32 → 0 < b →
        b ≤ 1 - s₂ → 3 / 4 < ρ → ρ + r₀ < 2 → 0 < τ → τ ≤ 1 → 0 < s₁ → s₁ < σ₀ →
        s₁ < s₂ → s₂ < 1 → 2 * (1 - s₂) ≤ b₅ → 0 < c →
        HasAlignedFluxIdentification g u (phasePrimitive f 1) ℓ r₀ b ρ τ s₁ s₂ L c K →
        HasAlignedHeightMoments g u ℓ r₀ b ρ τ s₁ s₂ L c K := by
  obtain ⟨b₅, σ₀, hb₅, hσ₀, hmain⟩ := hr.tendsto_alignedHeightMoment h hsharp
  refine ⟨b₅, σ₀, hb₅, hσ₀, ?_⟩
  intro ℓ r₀ b ρ τ s₁ s₂ c K L hℓ hr₀ hr₀' hb hbs₂ hρ hρr₀ hτ hτ1 hs₁ hs₁σ hs₁₂ hs₂ hb₅s hc
    hC x R Q δ e hal φ σl a H hlim
  exact ⟨hr.tendsto_alignedCenter_zero h hsharp hℓ hb.le (by linarith) (by linarith) hτ hs₁ hs₂
      (by rw [abs_of_pos hr₀]; exact hρr₀) hal hlim,
    hmain ℓ r₀ b ρ τ s₁ s₂ c K L hℓ hr₀ hr₀' hb hbs₂ hρ hρr₀ hτ hτ1 hs₁ hs₁σ hs₁₂ hs₂ hb₅s hc
      hC x R Q δ e hal φ σl a H hlim⟩

end SerrinEpigraph
