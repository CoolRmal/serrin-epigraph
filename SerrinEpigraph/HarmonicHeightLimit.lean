module

public import SerrinEpigraph.HarmonicHeightEstimates
public import SerrinEpigraph.SobolevBallCompactness
public import SerrinEpigraph.HarmonicWeyl

/-!
# The harmonic limit of normalized heights (`GR11`)

For a normalized configuration (`SlabTrappedRepresentation` on `B_2 × (-H', H')`), `GR9` with
`κ = 1/2` gives a Lipschitz approximation `f` of the signed height `g` on a good set `G`. Let
`c = ⨍_{B_{3/2}} f` and `e = ε(B_2)`.

* `integral_abs_sub_average_le_of_approx`, `IsLocalPerimeterMinimizer.band_of_approx`: the band
  around `c` (`GR10` recentred at `c`), and the phase outside the band.
* `SlabTrappedRepresentation.integral_height_sq_le_of_approx` (`GR11.1` for one configuration):
  `∫ η (x_n - c - s ℓ)² dμ ≤ 2 ∫ η (f - c - s ℓ)² + δ'² (8·4^m + 1) e`.
* `IsLocalPerimeterMinimizer.gr11_harmonic_limit` (**`GR11`**): for a sequence of normalized
  configurations through the origin with excess `e_j → 0`, a subsequence of the normalized heights
  `(f_j - c_j)/√e_j` converges in `L²` to a harmonic function `z` on `B_{3/2}`; the boundary lies in
  bands `|t - c_j| ≤ δ_j` with `c_j, δ_j → 0`; and for every affine `ℓ` and cutoff `η` supported in
  `B_{1/2}`, eventually `∫ η (x_n - c_j - √e_j ℓ)² dμ_j ≤ e_j (4 ∫ η (z - ℓ)² + ε)`.

The weak harmonicity of the limit comes from `abs_integral_columnSignedHeight_mul_laplacian_le`
(first variation and horizontal moment formula); no graph area formula is used.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal Laplacian

namespace SerrinEpigraph

/-! ### Laplacians of test functions -/

theorem laplacian_apply_eq_zero_of_notMem_tsupport {d : ℕ} {ψ : Space d → ℝ} {y : Space d}
    (hy : y ∉ tsupport ψ) : Δ ψ y = 0 := by
  have hev : ψ =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hy] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  rw [(laplacian_congr_nhds hev).eq_of_nhds]
  simp

theorem hasCompactSupport_laplacian {d : ℕ} {ψ : Space d → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (Δ ψ) :=
  hψc.mono' fun y hy ↦ by
    by_contra hn
    exact hy (laplacian_apply_eq_zero_of_notMem_tsupport hn)

theorem integral_laplacian_eq_zero {d : ℕ} {ψ : Space d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) : ∫ y, Δ ψ y = 0 := by
  have h := integral_inner_gradient_eq_neg_integral_mul_laplacian_of_lipschitz
    (f := fun _ : Space d ↦ (1 : ℝ)) (LipschitzWith.const (1 : ℝ)) hψ hψc
  have hg : ∀ y, gradient (fun _ : Space d ↦ (1 : ℝ)) y = 0 := fun y ↦ by simp [gradient]
  simp only [hg, inner_zero_left, integral_zero, one_mul] at h
  linarith

/-- Changing a bounded function off a set `G` changes `∫ f Δψ` by at most `2 H sup|Δψ| |B \ G|`. -/
theorem abs_integral_sub_mul_laplacian_le {d : ℕ} {f g : Space d → ℝ} {G B : Set (Space d)}
    (hBm : MeasurableSet B) (hBfin : volume B ≠ ⊤) (hGm : MeasurableSet G)
    (hfm : AEStronglyMeasurable f volume) (hgm : AEStronglyMeasurable g volume) {H : ℝ}
    (hf : ∀ y, |f y| ≤ H) (hg : ∀ y, |g y| ≤ H) (hfg : ∀ᵐ y ∂volume, y ∈ G → f y = g y)
    {ψ : Space d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (hψB : tsupport ψ ⊆ B)
    {M : ℝ} (hM : ∀ y, |Δ ψ y| ≤ M) :
    |(∫ y, f y * Δ ψ y) - ∫ y, g y * Δ ψ y| ≤ 2 * H * M * volume.real (B \ G) := by
  have hΔi : Integrable (Δ ψ) :=
    (continuous_laplacian_of_contDiff hψ).integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian hψc)
  have hfi : Integrable (fun y ↦ f y * Δ ψ y) :=
    hΔi.bdd_mul (c := H) hfm (Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hf y)
  have hgi : Integrable (fun y ↦ g y * Δ ψ y) :=
    hΔi.bdd_mul (c := H) hgm (Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hg y)
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hf 0)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hBG : volume (B \ G) ≠ ⊤ := ((measure_mono sdiff_subset).trans_lt hBfin.lt_top).ne
  have hint : Integrable ((B \ G).indicator (fun _ ↦ 2 * H * M)) :=
    (integrableOn_const hBG).integrable_indicator (hBm.diff hGm)
  rw [← integral_sub hfi hgi]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |f y * Δ ψ y - g y * Δ ψ y|
      ≤ ∫ y, (B \ G).indicator (fun _ ↦ 2 * H * M) y := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _) hint ?_
        filter_upwards [hfg] with y hy
        by_cases hyB : y ∈ B
        · by_cases hyG : y ∈ G
          · rw [hy hyG, sub_self, abs_zero]
            exact indicator_nonneg (fun _ _ ↦ by positivity) _
          · rw [indicator_of_mem (show y ∈ B \ G from ⟨hyB, hyG⟩), ← sub_mul, abs_mul]
            have h1 : |f y - g y| ≤ 2 * H := by
              have hf' := abs_le.mp (hf y)
              have hg' := abs_le.mp (hg y)
              rw [abs_le]
              constructor <;> linarith
            exact mul_le_mul h1 (hM y) (abs_nonneg _) (by positivity)
        · have hy0 : Δ ψ y = 0 :=
            laplacian_apply_eq_zero_of_notMem_tsupport (fun h ↦ hyB (hψB h))
          rw [hy0, mul_zero, mul_zero, sub_zero, abs_zero]
          exact indicator_nonneg (fun _ _ ↦ by positivity) _
    _ = 2 * H * M * volume.real (B \ G) := by
        rw [integral_indicator (hBm.diff hGm), setIntegral_const, smul_eq_mul, mul_comm]

/-! ### The Lipschitz approximation with `κ = 1/2` -/

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

theorem gradApproxConst_nonneg (m : ℕ) : 0 ≤ gradApproxConst m := by
  unfold gradApproxConst
  positivity

/-- `GR9` with `κ = 1/2`, with the trivial approximation `f = 0` when `e > 1/2`. -/
theorem exists_gr9_data (hS : SlabTrappedRepresentation b E U H H' μ ν)
    (hU2 : ball (0 : Space m) 2 ⊆ U) :
    ∃ (G : Set (Space m)) (f : Space m → ℝ),
      LipschitzWith (Real.toNNReal (lipschitzApproxConst m * Real.sqrt (1 / 2))) f ∧
      (∀ y, |f y| ≤ H) ∧
      ∫ y in ball (0 : Space m) (3 / 2), ‖fderiv ℝ f y‖ ^ 2 ≤
        gradApproxConst m * (projectedExcessMeasure μ ν).real (ball 0 2) ∧
      ((projectedExcessMeasure μ ν).real (ball 0 2) ≤ 1 / 2 →
        MeasurableSet G ∧ G ⊆ ball 0 (3 / 2) ∧
        volume.real (ball (0 : Space m) (3 / 2) \ G) ≤
          2 * 4 ^ m * (projectedExcessMeasure μ ν).real (ball 0 2) ∧
        (∀ᵐ y ∂volume, y ∈ G → f y = columnSignedHeight E H y) ∧
        (∀ᵐ x ∂volume, x ∈ cylinderSet U H' → horizontal x ∈ G →
          (x ∈ E ↔ f (horizontal x) < x (Fin.last m)))) := by
  by_cases he : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ 1 / 2
  · obtain ⟨hGm, hGs, hGv, -, f, hfL, hfH, hfg, hfE, hfD⟩ :=
      hS.gr9_lipschitz_approximation hU2 (κ := 1 / 2) (by norm_num) (by norm_num) he
    refine ⟨_, f, hfL, hfH, hfD, fun _ ↦ ⟨hGm, hGs, ?_, hfg, hfE⟩⟩
    calc _ ≤ 4 ^ m / (1 / 2) * (projectedExcessMeasure μ ν).real (ball 0 2) := hGv
      _ = 2 * 4 ^ m * (projectedExcessMeasure μ ν).real (ball 0 2) := by ring
  · refine ⟨∅, fun _ ↦ 0, (LipschitzWith.const (0 : ℝ)).weaken zero_le,
      fun _ ↦ by simp [hS.pos.le], ?_, fun h ↦ absurd h he⟩
    have h0 : ∀ y, fderiv ℝ (fun _ : Space m ↦ (0 : ℝ)) y = 0 := fun y ↦ fderiv_const_apply 0
    simp only [h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
    exact mul_nonneg (gradApproxConst_nonneg m) measureReal_nonneg

end SlabTrappedRepresentation

open SlabTrappedRepresentation in
/-- The constant `C₁` in `∫_{B_1} |g - c| ≤ C₁ √e`. -/
def gr11BandConst (m : ℕ) (H : ℝ) : ℝ :=
  2 * H * (2 * 4 ^ m) + Real.sqrt (volume.real (ball (0 : Space m) (3 / 2)) *
    (2 ^ (m + 1) * (3 / 2) ^ 2) * gradApproxConst m)

/-- The band width `δ(e)` around the average of the Lipschitz approximation. -/
def gr11BandWidth (m : ℕ) (H H' e : ℝ) : ℝ :=
  ((gr11BandConst m H * Real.sqrt e + 2 * H' * e) / minimizerVolumeDensityConst m) ^
    ((1 : ℝ) / (m + 1))

theorem gr11BandWidth_nonneg (m : ℕ) {H H' e : ℝ} (hH : 0 ≤ H) (hH' : 0 ≤ H') (he : 0 ≤ e) :
    0 ≤ gr11BandWidth m H H' e := by
  unfold gr11BandWidth gr11BandConst
  have := minimizerVolumeDensityConst_pos m
  positivity

theorem tendsto_gr11BandWidth (m : ℕ) (H H' : ℝ) :
    Tendsto (gr11BandWidth m H H') (𝓝 0) (𝓝 0) := by
  have h1 : Tendsto (fun e : ℝ ↦ (gr11BandConst m H * Real.sqrt e + 2 * H' * e) /
      minimizerVolumeDensityConst m) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun e : ℝ ↦ (gr11BandConst m H * Real.sqrt e + 2 * H' * e) /
        minimizerVolumeDensityConst m) := by fun_prop
    simpa using hc.tendsto 0
  have h2 : Tendsto (fun x : ℝ ↦ x ^ ((1 : ℝ) / (m + 1))) (𝓝 0) (𝓝 0) := by
    have hq : (0 : ℝ) < 1 / (m + 1) := by positivity
    have := (Real.continuousAt_rpow_const 0 ((1 : ℝ) / (m + 1)) (Or.inr hq.le)).tendsto
    rwa [Real.zero_rpow hq.ne'] at this
  exact h2.comp h1

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- `∫_{B_1} |g - c| ≤ C₁ √e` for the average `c = ⨍_{B_{3/2}} f` of the approximation. -/
theorem integral_abs_sub_average_le_of_approx (hS : SlabTrappedRepresentation b E U H H' μ ν)
    {G : Set (Space m)} {f : Space m → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (hfH : ∀ y, |f y| ≤ H) (hGm : MeasurableSet G)
    (hGB : volume.real (ball (0 : Space m) (3 / 2) \ G) ≤
      2 * 4 ^ m * (projectedExcessMeasure μ ν).real (ball 0 2))
    (hfg : ∀ᵐ y ∂volume, y ∈ G → f y = columnSignedHeight E H y)
    (hD : ∫ y in ball (0 : Space m) (3 / 2), ‖fderiv ℝ f y‖ ^ 2 ≤
      gradApproxConst m * (projectedExcessMeasure μ ν).real (ball 0 2))
    (he1 : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ 1) :
    ∫ y in ball (0 : Space m) 1,
        |columnSignedHeight E H y - ⨍ z in ball (0 : Space m) (3 / 2), f z| ≤
      gr11BandConst m H * Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) := by
  set e := (projectedExcessMeasure μ ν).real (ball (0 : Space m) 2) with he_def
  set c := ⨍ z in ball (0 : Space m) (3 / 2), f z with hc_def
  set g := columnSignedHeight E H with hg_def
  set B := ball (0 : Space m) (3 / 2) with hB_def
  have hH0 : 0 ≤ H := hS.pos.le
  have he0 : 0 ≤ e := measureReal_nonneg
  have hgm : Measurable g := measurable_columnSignedHeight hS.measurableSet H
  have hgH : ∀ y, |g y| ≤ H := abs_columnSignedHeight_le E hH0
  have hfm : Measurable f := hf.continuous.measurable
  have hB1 : ball (0 : Space m) 1 ⊆ B := ball_subset_ball (by norm_num)
  have hBfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hcH : |c| ≤ H := abs_setAverage_le_of_abs_le measure_ball_lt_top hfH
  -- integrability of the bounded integrands on `B`
  have hint_gf : IntegrableOn (fun y ↦ |g y - f y|) B := by
    refine Measure.integrableOn_of_bounded (M := 2 * H) hBfin
      ((continuous_abs.measurable.comp (hgm.sub hfm)).aestronglyMeasurable) (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_le.mp (hgH y)
    have h2 := abs_le.mp (hfH y)
    rw [abs_le]
    constructor <;> linarith
  have hint_fc : IntegrableOn (fun y ↦ |f y - c|) B := by
    refine Measure.integrableOn_of_bounded (M := 2 * H) hBfin
      ((continuous_abs.measurable.comp (hfm.sub measurable_const)).aestronglyMeasurable)
      (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_le.mp hcH
    have h2 := abs_le.mp (hfH y)
    rw [abs_le]
    constructor <;> linarith
  -- the bad set term
  have hbad : ∫ y in B, |g y - f y| ≤ 2 * H * (2 * 4 ^ m * e) := by
    have hBG : volume (B \ G) ≠ ⊤ := ((measure_mono sdiff_subset).trans_lt hBfin.lt_top).ne
    have hle : ∀ᵐ y ∂(volume.restrict B), |g y - f y| ≤ (B \ G).indicator (fun _ ↦ 2 * H) y := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [hfg] with y hy hyB
      by_cases hyG : y ∈ G
      · rw [hy hyG, sub_self, abs_zero]
        exact indicator_nonneg (fun _ _ ↦ by positivity) _
      · rw [indicator_of_mem (show y ∈ B \ G from ⟨hyB, hyG⟩)]
        have h1 := abs_le.mp (hgH y)
        have h2 := abs_le.mp (hfH y)
        rw [abs_le]
        constructor <;> linarith
    have hint : Integrable ((B \ G).indicator (fun _ ↦ 2 * H)) :=
      (integrableOn_const hBG).integrable_indicator (measurableSet_ball.diff hGm)
    calc ∫ y in B, |g y - f y| ≤ ∫ y in B, (B \ G).indicator (fun _ ↦ 2 * H) y :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _)
            hint.integrableOn hle
      _ ≤ ∫ y, (B \ G).indicator (fun _ ↦ 2 * H) y :=
          setIntegral_le_integral hint
            (Eventually.of_forall fun _ ↦ indicator_nonneg (fun _ _ ↦ by positivity) _)
      _ = 2 * H * volume.real (B \ G) := by
          rw [integral_indicator (measurableSet_ball.diff hGm), setIntegral_const, smul_eq_mul,
            mul_comm]
      _ ≤ 2 * H * (2 * 4 ^ m * e) := mul_le_mul_of_nonneg_left hGB (by positivity)
  -- the oscillation term, by Cauchy–Schwarz and Poincaré
  have hosc : ∫ y in B, |f y - c| ≤
      Real.sqrt (volume.real B * (2 ^ (m + 1) * (3 / 2) ^ 2) * gradApproxConst m) *
        Real.sqrt e := by
    have hP := poincare_ball (0 : Space m) (r := 3 / 2) (by norm_num) hf
    have := isFiniteMeasure_restrict.mpr hBfin
    have hsq : Integrable (fun y ↦ |f y - c| ^ 2) (volume.restrict B) := by
      refine Measure.integrableOn_of_bounded (M := (2 * H) ^ 2) hBfin
        (((continuous_abs.measurable.comp (hfm.sub measurable_const)).pow_const 2).aestronglyMeasurable)
        (Eventually.of_forall fun y ↦ ?_)
      rw [Real.norm_eq_abs, abs_pow, abs_abs]
      have h1 := abs_le.mp hcH
      have h2 := abs_le.mp (hfH y)
      have h3 : |f y - c| ≤ 2 * H := by
        rw [abs_le]
        constructor <;> linarith
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    have hCS := sq_integral_le_measureReal_mul_integral_sq hint_fc hsq
    have hreal : (volume.restrict B).real univ = volume.real B := by
      simp [Measure.real]
    rw [hreal] at hCS
    have hsq_eq : ∫ y in B, |f y - c| ^ 2 = ∫ y in B, (f y - c) ^ 2 := by
      congr 1
      ext y
      exact sq_abs _
    rw [hsq_eq] at hCS
    have hP' : ∫ y in B, (f y - c) ^ 2 ≤ 2 ^ (m + 1) * (3 / 2) ^ 2 * (gradApproxConst m * e) :=
      hP.trans (mul_le_mul_of_nonneg_left hD (by positivity))
    have hI0 : 0 ≤ ∫ y in B, |f y - c| := integral_nonneg fun _ ↦ abs_nonneg _
    rw [← Real.sqrt_mul (by have := gradApproxConst_nonneg m; positivity)]
    apply Real.le_sqrt_of_sq_le
    calc (∫ y in B, |f y - c|) ^ 2 ≤ volume.real B * ∫ y in B, (f y - c) ^ 2 := by
          simpa [Measure.real] using hCS
      _ ≤ volume.real B * (2 ^ (m + 1) * (3 / 2) ^ 2 * (gradApproxConst m * e)) :=
          mul_le_mul_of_nonneg_left hP' measureReal_nonneg
      _ = volume.real B * (2 ^ (m + 1) * (3 / 2) ^ 2) * gradApproxConst m * e := by ring
  have hsplit : ∫ y in ball (0 : Space m) 1, |g y - c| ≤
      (∫ y in B, |g y - f y|) + ∫ y in B, |f y - c| := by
    calc ∫ y in ball (0 : Space m) 1, |g y - c|
        ≤ ∫ y in ball (0 : Space m) 1, (|g y - f y| + |f y - c|) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _)
            ((hint_gf.mono_set hB1).add (hint_fc.mono_set hB1))
            (Eventually.of_forall fun y ↦ ?_)
          calc |g y - c| = |(g y - f y) + (f y - c)| := by ring_nf
            _ ≤ |g y - f y| + |f y - c| := abs_add_le _ _
      _ = (∫ y in ball (0 : Space m) 1, |g y - f y|) + ∫ y in ball (0 : Space m) 1, |f y - c| :=
          integral_add (hint_gf.mono_set hB1) (hint_fc.mono_set hB1)
      _ ≤ (∫ y in B, |g y - f y|) + ∫ y in B, |f y - c| :=
          add_le_add
            (setIntegral_mono_set hint_gf (Eventually.of_forall fun _ ↦ abs_nonneg _)
              (Eventually.of_forall hB1))
            (setIntegral_mono_set hint_fc (Eventually.of_forall fun _ ↦ abs_nonneg _)
              (Eventually.of_forall hB1))
  have hesq : e ≤ Real.sqrt e := by
    have h1 : Real.sqrt e ≤ 1 := Real.sqrt_le_one.mpr he1
    calc e = Real.sqrt e * Real.sqrt e := (Real.mul_self_sqrt he0).symm
      _ ≤ 1 * Real.sqrt e := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      _ = Real.sqrt e := one_mul _
  calc ∫ y in ball (0 : Space m) 1, |g y - c|
      ≤ 2 * H * (2 * 4 ^ m * e) +
          Real.sqrt (volume.real B * (2 ^ (m + 1) * (3 / 2) ^ 2) * gradApproxConst m) *
            Real.sqrt e := hsplit.trans (add_le_add hbad hosc)
    _ ≤ 2 * H * (2 * 4 ^ m) * Real.sqrt e +
          Real.sqrt (volume.real B * (2 ^ (m + 1) * (3 / 2) ^ 2) * gradApproxConst m) *
            Real.sqrt e := by
        have : 2 * H * (2 * 4 ^ m * e) = 2 * H * (2 * 4 ^ m) * e := by ring
        rw [this]
        gcongr
    _ = gr11BandConst m H * Real.sqrt e := by
        rw [gr11BandConst]
        ring

end SlabTrappedRepresentation

namespace IsLocalPerimeterMinimizer

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **The band around the average of the approximation** (`GR10` recentred). -/
theorem band_of_approx (hmin : IsLocalPerimeterMinimizer b E Ω)
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    (hcyl : cylinderSet U H' ⊆ Ω)
    {G : Set (Space m)} {f : Space m → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (hfH : ∀ y, |f y| ≤ H) (hGm : MeasurableSet G)
    (hGB : volume.real (ball (0 : Space m) (3 / 2) \ G) ≤
      2 * 4 ^ m * (projectedExcessMeasure μ ν).real (ball 0 2))
    (hfg : ∀ᵐ y ∂volume, y ∈ G → f y = columnSignedHeight E H y)
    (hD : ∫ y in ball (0 : Space m) (3 / 2), ‖fderiv ℝ f y‖ ^ 2 ≤
      SlabTrappedRepresentation.gradApproxConst m * (projectedExcessMeasure μ ν).real (ball 0 2))
    (he1 : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ 1) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hr₀1 : r₀ ≤ 1 / 4) (hr₀H : r₀ ≤ (H' - H) / 2)
    (hsmall : gr11BandConst m H * Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) +
      2 * H' * (projectedExcessMeasure μ ν).real (ball 0 2) <
        minimizerVolumeDensityConst m * r₀ ^ (m + 1)) :
    |⨍ z in ball (0 : Space m) (3 / 2), f z| ≤ H ∧
    (∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      |x (Fin.last m)| < H' →
      |x (Fin.last m) - ⨍ z in ball (0 : Space m) (3 / 2), f z| ≤
        gr11BandWidth m H H' ((projectedExcessMeasure μ ν).real (ball 0 2))) ∧
    (∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) (1 / 2) → |x (Fin.last m)| < H' →
      gr11BandWidth m H H' ((projectedExcessMeasure μ ν).real (ball 0 2)) <
        |x (Fin.last m) - ⨍ z in ball (0 : Space m) (3 / 2), f z| →
      (x ∈ E ↔ ⨍ z in ball (0 : Space m) (3 / 2), f z < x (Fin.last m))) := by
  set e := (projectedExcessMeasure μ ν).real (ball (0 : Space m) 2) with he_def
  set c := ⨍ z in ball (0 : Space m) (3 / 2), f z with hc_def
  have := hS.isFiniteMeasure_excess
  have hH0 : 0 ≤ H := hS.pos.le
  have hH'0 : 0 ≤ H' := (hS.pos.trans hS.lt).le
  have he0 : 0 ≤ e := measureReal_nonneg
  have hcH : |c| ≤ H := abs_setAverage_le_of_abs_le measure_ball_lt_top hfH
  have hU1 : ball (0 : Space m) 1 ⊆ U := (ball_subset_ball (by norm_num)).trans hU2
  have hosc := hS.integral_abs_sub_average_le_of_approx hf hfH hGm hGB hfg hD he1
  have hdisc := hS.volume_real_halfspaceDiscrepancy_le hU1 c
  have hε1 : (projectedExcessMeasure μ ν).real (ball (0 : Space m) 1) ≤ e :=
    measureReal_mono (ball_subset_ball (by norm_num)) (measure_ne_top _ _)
  have hV : volume.real (halfspaceDiscrepancy E H' c) ≤
      gr11BandConst m H * Real.sqrt e + 2 * H' * e := by
    have h2 : 2 * H' * (projectedExcessMeasure μ ν).real (ball (0 : Space m) 1) ≤ 2 * H' * e :=
      mul_le_mul_of_nonneg_left hε1 (by linarith)
    linarith
  have hc0 := minimizerVolumeDensityConst_pos m
  have hδ0 : 0 ≤ gr11BandWidth m H H' e := gr11BandWidth_nonneg m hH0 hH'0 he0
  have hband : ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      |x (Fin.last m)| < H' → |x (Fin.last m) - c| ≤ gr11BandWidth m H H' e := by
    intro x hx hxh hxn
    have hb := hmin.band_width_le hS hU1 hcyl c hr₀ hr₀1 hr₀H (hV.trans_lt hsmall) hx hxh hxn
    refine hb.trans ?_
    unfold gr11BandWidth
    exact Real.rpow_le_rpow (div_nonneg measureReal_nonneg hc0.le)
      (div_le_div_of_nonneg_right hV hc0.le) (by positivity)
  refine ⟨hcH, hband, ?_⟩
  exact hS.ae_mem_iff_of_band (convex_ball _ _)
    ((ball_subset_ball (by norm_num)).trans hU2) hcH hδ0 hband

end IsLocalPerimeterMinimizer

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **`GR11.1` for one normalized configuration.** With the band `|t - c| ≤ δ` over `B_{1/2}`,
for an affine level `L = c + s (a + ⟪p, y⟫)` with `|c| + s(|a| + ‖p‖) ≤ H`,
`∫ η (x_n - L)² dμ ≤ 2 ∫ η (f - L)² + (δ + s(|a| + ‖p‖))² (8·4^m + 1) e`. -/
theorem integral_height_sq_le_of_approx (hS : SlabTrappedRepresentation b E U H H' μ ν)
    (hU2 : ball (0 : Space m) 2 ⊆ U)
    {G : Set (Space m)} {f : Space m → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (hfH : ∀ y, |f y| ≤ H) (hGm : MeasurableSet G)
    (hGB : volume.real (ball (0 : Space m) (3 / 2) \ G) ≤
      2 * 4 ^ m * (projectedExcessMeasure μ ν).real (ball 0 2))
    (hfE : ∀ᵐ x ∂volume, x ∈ cylinderSet U H' → horizontal x ∈ G →
      (x ∈ E ↔ f (horizontal x) < x (Fin.last m)))
    {c δ : ℝ} (hδ : 0 ≤ δ)
    (hband : ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      |x (Fin.last m)| < H' → |x (Fin.last m) - c| ≤ δ)
    (hphase : ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      |x (Fin.last m)| < H' → δ < |x (Fin.last m) - c| → (x ∈ E ↔ c < x (Fin.last m)))
    {η : Space m → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηB : tsupport η ⊆ ball 0 (1 / 2)) (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1)
    {a s : ℝ} {p : Space m} (hs : 0 ≤ s) (hcH : |c| + s * (|a| + ‖p‖) ≤ H) :
    ∫ x, η (horizontal x) *
        (x (Fin.last m) - (c + s * (a + inner ℝ p (horizontal x)))) ^ 2 ∂μ ≤
      2 * (∫ y, η y * (f y - (c + s * (a + inner ℝ p y))) ^ 2) +
        (δ + s * (|a| + ‖p‖)) ^ 2 * (8 * 4 ^ m + 1) *
          (projectedExcessMeasure μ ν).real (ball 0 2) := by
  set e := (projectedExcessMeasure μ ν).real (ball (0 : Space m) 2) with he_def
  have := hS.isFiniteMeasure_excess
  set L : Space m → ℝ := fun y ↦ c + s * (a + inner ℝ p y) with hL_def
  set δ' := δ + s * (|a| + ‖p‖) with hδ'_def
  have hsa : 0 ≤ s * (|a| + ‖p‖) := mul_nonneg hs (by positivity)
  have hδ'0 : 0 ≤ δ' := by positivity
  have hLc : ∀ y ∈ ball (0 : Space m) (1 / 2), |L y - c| ≤ s * (|a| + ‖p‖) := by
    intro y hy
    have hy1 : ‖y‖ ≤ 1 := by
      have := mem_ball_zero_iff.mp hy
      linarith
    have hin : |inner ℝ p y| ≤ ‖p‖ := by
      calc |inner ℝ p y| ≤ ‖p‖ * ‖y‖ := abs_real_inner_le_norm p y
        _ ≤ ‖p‖ * 1 := mul_le_mul_of_nonneg_left hy1 (norm_nonneg _)
        _ = ‖p‖ := mul_one _
    have : L y - c = s * (a + inner ℝ p y) := by simp only [L]; ring
    rw [this, abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by linarith)) hs
  have hL : ContDiff ℝ 1 L := by
    have : ContDiff ℝ 1 (fun y : Space m ↦ inner ℝ p y) := (innerSL ℝ p).contDiff
    exact contDiff_const.add (contDiff_const.mul (contDiff_const.add this))
  have hLH : ∀ y ∈ ball (0 : Space m) (1 / 2), |L y| ≤ H := by
    intro y hy
    calc |L y| = |c + (L y - c)| := by ring_nf
      _ ≤ |c| + |L y - c| := abs_add_le _ _
      _ ≤ |c| + s * (|a| + ‖p‖) := by linarith [hLc y hy]
      _ ≤ H := hcH
  have hbandμ : ∀ᵐ x ∂μ, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      |x (Fin.last m) - L (horizontal x)| ≤ δ' := by
    filter_upwards [hS.ae_abs_last_le] with x hx hxB
    have h1 := hband x hx.1 hxB (abs_lt.mpr hx.2.1.2)
    have h2 := hLc _ hxB
    calc |x (Fin.last m) - L (horizontal x)|
        = |(x (Fin.last m) - c) - (L (horizontal x) - c)| := by ring_nf
      _ ≤ |x (Fin.last m) - c| + |L (horizontal x) - c| := abs_sub _ _
      _ ≤ δ' := by linarith
  have hbandE : ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      |x (Fin.last m)| < H' → δ' < |x (Fin.last m) - L (horizontal x)| →
      (x ∈ E ↔ L (horizontal x) < x (Fin.last m)) := by
    filter_upwards [hphase] with x hx hxB hxH hxδ
    have h2 := hLc _ hxB
    set t := x (Fin.last m)
    set l := L (horizontal x)
    have hgap : δ < |t - c| := by
      have : |t - l| ≤ |t - c| + |l - c| := by
        calc |t - l| = |(t - c) - (l - c)| := by ring_nf
          _ ≤ |t - c| + |l - c| := abs_sub _ _
      linarith
    rw [hx hxB hxH hgap]
    have h2' := abs_le.mp h2
    rcases lt_or_gt_of_ne (show t - l ≠ 0 from fun h0 ↦ by
      rw [h0, abs_zero] at hxδ; linarith) with hneg | hpos
    · rw [abs_of_neg hneg] at hxδ
      constructor <;> intro h <;> linarith
    · rw [abs_of_pos hpos] at hxδ
      constructor <;> intro h <;> linarith
  have hmain := hS.integral_height_sq_le measurableSet_ball measure_ball_lt_top.ne
    ((ball_subset_ball (by norm_num)).trans hU2) hη hηc hηB hη0 hη1 hL hLH hδ'0 hbandμ hbandE
    hGm hf.continuous.measurable hfH hfE
  have hηfL : Integrable (fun y ↦ η y * (f y - L y) ^ 2) :=
    (hη.continuous.mul ((hf.continuous.sub hL.continuous).pow 2)).integrable_of_hasCompactSupport
      (hηc.mul_right)
  have hG_le : ∫ y in G, η y * (f y - L y) ^ 2 ≤ ∫ y, η y * (f y - L y) ^ 2 :=
    setIntegral_le_integral hηfL (Eventually.of_forall fun y ↦ mul_nonneg (hη0 y) (sq_nonneg _))
  have hBG : volume.real (ball (0 : Space m) (1 / 2) \ G) ≤ 2 * 4 ^ m * e :=
    (measureReal_mono (sdiff_subset_sdiff_left (ball_subset_ball (by norm_num)))
      ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne).trans hGB
  have hεB : (projectedExcessMeasure μ ν).real (ball (0 : Space m) (1 / 2)) ≤ e :=
    measureReal_mono (ball_subset_ball (by norm_num)) (measure_ne_top _ _)
  calc ∫ x, η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2 ∂μ
      ≤ 2 * (∫ y in G, η y * (f y - L y) ^ 2) +
          4 * δ' ^ 2 * volume.real (ball (0 : Space m) (1 / 2) \ G) +
          δ' ^ 2 * (projectedExcessMeasure μ ν).real (ball 0 (1 / 2)) := hmain
    _ ≤ 2 * (∫ y, η y * (f y - L y) ^ 2) + 4 * δ' ^ 2 * (2 * 4 ^ m * e) + δ' ^ 2 * e := by
        gcongr
    _ = 2 * (∫ y, η y * (f y - L y) ^ 2) + δ' ^ 2 * (8 * 4 ^ m + 1) * e := by ring

end SlabTrappedRepresentation

end SerrinEpigraph
