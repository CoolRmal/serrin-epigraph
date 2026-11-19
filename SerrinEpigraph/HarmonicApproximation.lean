module

public import SerrinEpigraph.HarmonicHeightLimit

/-!
# `GR11`: the harmonic limit of normalized heights

`IsLocalPerimeterMinimizer.gr11_harmonic_limit`: for a sequence of normalized configurations
through the origin with excess `e_j → 0`, a subsequence of the normalized heights
`(f_j - c_j)/√e_j` converges in `L²` to a harmonic function `z` on `B_{3/2}`, the boundary lies in
bands `|t - c_j| ≤ δ_j` with `c_j, δ_j → 0`, and the height square on the perimeter measure is
controlled by the harmonic limit (`GR11.1`, upper bound).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal Laplacian

namespace SerrinEpigraph

theorem sq_sub_le_two_mul_add (u v l : ℝ) : (u - l) ^ 2 ≤ 2 * (v - l) ^ 2 + 2 * (u - v) ^ 2 := by
  nlinarith [sq_nonneg ((v - l) - (u - v))]

theorem sq_le_two_mul_add (u v : ℝ) : v ^ 2 ≤ 2 * u ^ 2 + 2 * (u - v) ^ 2 := by
  nlinarith [sq_nonneg (u + (u - v))]

theorem horizontal_zero {m : ℕ} : horizontal (0 : Space (m + 1)) = 0 := by
  ext i
  simp [horizontal]

/-! ### Normalized heights -/

theorem lipschitzWith_normalized {d : ℕ} {f : Space d → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    {c s : ℝ} (hs : 0 < s) :
    LipschitzWith (Real.toNNReal s⁻¹ * K) (fun y ↦ s⁻¹ * (f y - c)) := by
  refine LipschitzWith.of_dist_le_mul fun y y' ↦ ?_
  have h1 := hf.dist_le_mul y y'
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.mpr hs.le)]
  simp only [Real.dist_eq] at h1 ⊢
  rw [show s⁻¹ * (f y - c) - s⁻¹ * (f y' - c) = s⁻¹ * (f y - f y') by ring, abs_mul,
    abs_of_pos (inv_pos.mpr hs), mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hs.le)

theorem fderiv_normalized {d : ℕ} (f : Space d → ℝ) (c s : ℝ) (y : Space d) :
    fderiv ℝ (fun y ↦ s⁻¹ * (f y - c)) y = s⁻¹ • fderiv ℝ f y := by
  have h1 : (fun y ↦ s⁻¹ * (f y - c)) = s⁻¹ • (fun y ↦ f y - c) := by
    funext y
    simp [smul_eq_mul]
  rw [h1, fderiv_const_smul_field, Pi.smul_apply, fderiv_sub_const]

/-- `L²` and energy bounds for the normalized height `(f - f_{B_{3/2}})/√e`. -/
theorem normalized_bounds {m : ℕ} {f : Space m → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    {e Cg : ℝ} (he : 0 < e)
    (hD : ∫ y in ball (0 : Space m) (3 / 2), ‖fderiv ℝ f y‖ ^ 2 ≤ Cg * e) :
    ∫ y in ball (0 : Space m) (3 / 2),
        ((Real.sqrt e)⁻¹ * (f y - ⨍ z in ball (0 : Space m) (3 / 2), f z)) ^ 2 ≤
      2 ^ (m + 1) * (3 / 2) ^ 2 * Cg ∧
    ∫ y in ball (0 : Space m) (3 / 2),
        ‖fderiv ℝ (fun y ↦ (Real.sqrt e)⁻¹ * (f y - ⨍ z in ball (0 : Space m) (3 / 2), f z)) y‖ ^ 2
      ≤ Cg := by
  set c := ⨍ z in ball (0 : Space m) (3 / 2), f z
  have hs : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hP := poincare_ball (0 : Space m) (by norm_num : (0 : ℝ) < 3 / 2) hf
  constructor
  · have hpt : ∀ y, ((Real.sqrt e)⁻¹ * (f y - c)) ^ 2 = e⁻¹ * (f y - c) ^ 2 := by
      intro y
      rw [mul_pow, inv_pow, Real.sq_sqrt he.le]
    simp_rw [hpt]
    rw [integral_const_mul]
    calc e⁻¹ * ∫ y in ball (0 : Space m) (3 / 2), (f y - c) ^ 2
        ≤ e⁻¹ * (2 ^ (m + 1) * (3 / 2) ^ 2 * (Cg * e)) :=
          mul_le_mul_of_nonneg_left (hP.trans (mul_le_mul_of_nonneg_left hD (by positivity)))
            (inv_nonneg.mpr he.le)
      _ = 2 ^ (m + 1) * (3 / 2) ^ 2 * Cg := by field_simp
  · have hpt : ∀ y, ‖fderiv ℝ (fun y ↦ (Real.sqrt e)⁻¹ * (f y - c)) y‖ ^ 2 =
        e⁻¹ * ‖fderiv ℝ f y‖ ^ 2 := by
      intro y
      rw [fderiv_normalized, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), mul_pow,
        inv_pow, Real.sq_sqrt he.le]
    simp_rw [hpt]
    rw [integral_const_mul]
    calc e⁻¹ * ∫ y in ball (0 : Space m) (3 / 2), ‖fderiv ℝ f y‖ ^ 2 ≤ e⁻¹ * (Cg * e) :=
          mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr he.le)
      _ = Cg := by field_simp

/-- Green's identity for the normalized height: `|∫ ⟨∇z, ∇ψ⟩| ≤ s⁻¹ |∫ f Δψ|`. -/
theorem norm_integral_inner_gradient_normalized_le {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {H : ℝ} (hfH : ∀ y, |f y| ≤ H) {c s : ℝ} (hs : 0 < s)
    {ψ : Space d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) {A : ℝ}
    (hA : |∫ y, f y * Δ ψ y| ≤ A) :
    ‖∫ y, inner ℝ (gradient (fun y ↦ s⁻¹ * (f y - c)) y) (gradient ψ y)‖ ≤ s⁻¹ * A := by
  rw [integral_inner_gradient_eq_neg_integral_mul_laplacian_of_lipschitz
    (lipschitzWith_normalized hf (c := c) hs) hψ hψc, norm_neg, Real.norm_eq_abs]
  have hΔi : Integrable (Δ ψ) :=
    (continuous_laplacian_of_contDiff hψ).integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian hψc)
  have hfi : Integrable (fun y ↦ f y * Δ ψ y) :=
    hΔi.bdd_mul (c := H) hf.continuous.aestronglyMeasurable
      (Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hfH y)
  have heq : ∫ y, s⁻¹ * (f y - c) * Δ ψ y = s⁻¹ * ∫ y, f y * Δ ψ y := by
    have hpt : ∀ y, s⁻¹ * (f y - c) * Δ ψ y = s⁻¹ * (f y * Δ ψ y - c * Δ ψ y) := by
      intro y
      ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_sub hfi (hΔi.const_mul _), integral_const_mul,
      integral_laplacian_eq_zero hψ hψc, mul_zero, sub_zero]
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hs)]
  exact mul_le_mul_of_nonneg_left hA (inv_nonneg.mpr hs.le)

/-- `∫ η (u - ℓ)² ≤ 2 ∫ η (v - ℓ)² + 2 ∫_B (u - v)²` for `0 ≤ η ≤ 1` supported in `B`. -/
theorem integral_mul_sq_le_of_approx {d : ℕ} {B : Set (Space d)} (hBm : MeasurableSet B)
    {η u v l : Space d → ℝ} (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1)
    (hηB : ∀ y, y ∉ B → η y = 0)
    (hu : Integrable (fun y ↦ η y * (u y - l y) ^ 2))
    (hv : Integrable (fun y ↦ η y * (v y - l y) ^ 2))
    (huv : IntegrableOn (fun y ↦ (u y - v y) ^ 2) B) :
    ∫ y, η y * (u y - l y) ^ 2 ≤
      2 * (∫ y, η y * (v y - l y) ^ 2) + 2 * ∫ y in B, (u y - v y) ^ 2 := by
  have hint_r : Integrable (fun y ↦ 2 * (η y * (v y - l y) ^ 2) +
      B.indicator (fun y ↦ 2 * (u y - v y) ^ 2) y) :=
    (hv.const_mul 2).add (IntegrableOn.integrable_indicator (huv.const_mul 2) hBm)
  calc ∫ y, η y * (u y - l y) ^ 2
      ≤ ∫ y, (2 * (η y * (v y - l y) ^ 2) + B.indicator (fun y ↦ 2 * (u y - v y) ^ 2) y) := by
        refine integral_mono hu hint_r fun y ↦ ?_
        by_cases hyB : y ∈ B
        · rw [indicator_of_mem hyB]
          have h1 := hη0 y
          have h2 := hη1 y
          have hsq := sq_sub_le_two_mul_add (u y) (v y) (l y)
          have hd : 0 ≤ (u y - v y) ^ 2 := sq_nonneg _
          calc η y * (u y - l y) ^ 2
              ≤ η y * (2 * (v y - l y) ^ 2 + 2 * (u y - v y) ^ 2) :=
                mul_le_mul_of_nonneg_left hsq h1
            _ = 2 * (η y * (v y - l y) ^ 2) + η y * (2 * (u y - v y) ^ 2) := by ring
            _ ≤ 2 * (η y * (v y - l y) ^ 2) + 1 * (2 * (u y - v y) ^ 2) := by
                gcongr
            _ = 2 * (η y * (v y - l y) ^ 2) + 2 * (u y - v y) ^ 2 := by ring
        · rw [indicator_of_notMem hyB, hηB y hyB]
          simp
    _ = 2 * (∫ y, η y * (v y - l y) ^ 2) + 2 * ∫ y in B, (u y - v y) ^ 2 := by
        rw [integral_add (hv.const_mul 2) (IntegrableOn.integrable_indicator (huv.const_mul 2) hBm),
          integral_const_mul, integral_indicator hBm, integral_const_mul]

/-- If `∫_B u_j² ≤ A` and `u_j → z` in `L²(B)`, then `∫_B z² ≤ 2A`. -/
theorem integral_sq_le_of_tendsto {d : ℕ} {B : Set (Space d)} {u : ℕ → Space d → ℝ}
    {z : Space d → ℝ} {A : ℝ} (hz : IntegrableOn (fun y ↦ z y ^ 2) B)
    (hu : ∀ j, IntegrableOn (fun y ↦ u j y ^ 2) B)
    (huz : ∀ j, IntegrableOn (fun y ↦ (u j y - z y) ^ 2) B)
    (hA : ∀ j, ∫ y in B, u j y ^ 2 ≤ A)
    (hlim : Tendsto (fun j ↦ ∫ y in B, (u j y - z y) ^ 2) atTop (𝓝 0)) :
    ∫ y in B, z y ^ 2 ≤ 2 * A := by
  have hbound : ∀ j, ∫ y in B, z y ^ 2 ≤ 2 * A + 2 * ∫ y in B, (u j y - z y) ^ 2 := by
    intro j
    calc ∫ y in B, z y ^ 2 ≤ ∫ y in B, (2 * u j y ^ 2 + 2 * (u j y - z y) ^ 2) :=
          integral_mono hz (((hu j).const_mul 2).add ((huz j).const_mul 2))
            fun y ↦ sq_le_two_mul_add (u j y) (z y)
      _ = 2 * (∫ y in B, u j y ^ 2) + 2 * ∫ y in B, (u j y - z y) ^ 2 := by
          rw [integral_add ((hu j).const_mul 2) ((huz j).const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * A + 2 * ∫ y in B, (u j y - z y) ^ 2 := by linarith [hA j]
  have hT : Tendsto (fun j ↦ 2 * A + 2 * ∫ y in B, (u j y - z y) ^ 2) atTop (𝓝 (2 * A)) := by
    simpa using (hlim.const_mul 2).const_add (2 * A)
  exact ge_of_tendsto' hT hbound

/-! ### Per-configuration estimates -/

namespace IsLocalPerimeterMinimizer

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

open SlabTrappedRepresentation in
/-- **Approximate harmonicity of the Lipschitz approximation**:
`|∫ f Δψ| ≤ (sup‖Dψ‖ + 4^{m+1} H sup|Δψ|) e`. -/
theorem abs_integral_approx_mul_laplacian_le (hmin : IsLocalPerimeterMinimizer b E Ω)
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    (hcyl : cylinderSet U H' ⊆ Ω) {G : Set (Space m)} {f : Space m → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hfH : ∀ y, |f y| ≤ H) (hGm : MeasurableSet G)
    (hGv : volume.real (ball (0 : Space m) (3 / 2) \ G) ≤
      2 * 4 ^ m * (projectedExcessMeasure μ ν).real (ball 0 2))
    (hfg : ∀ᵐ y ∂volume, y ∈ G → f y = columnSignedHeight E H y)
    {ψ : Space m → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ ball 0 (3 / 2)) {Kψ MΔ : ℝ} (hKψ : ∀ y, ‖fderiv ℝ ψ y‖ ≤ Kψ)
    (hMΔ : ∀ y, |Δ ψ y| ≤ MΔ) :
    |∫ y, f y * Δ ψ y| ≤
      (Kψ + 2 * H * MΔ * (2 * 4 ^ m)) * (projectedExcessMeasure μ ν).real (ball 0 2) := by
  have := hS.isFiniteMeasure_excess
  have hKψ0 : 0 ≤ Kψ := (norm_nonneg _).trans (hKψ 0)
  have hMΔ0 : 0 ≤ MΔ := (abs_nonneg _).trans (hMΔ 0)
  have hH0 : 0 ≤ H := hS.pos.le
  set e := (projectedExcessMeasure μ ν).real (ball (0 : Space m) 2) with he_def
  have hgΔ := hmin.abs_integral_columnSignedHeight_mul_laplacian_le hS hcyl measurableSet_ball
    ((ball_subset_ball (by norm_num)).trans hU2) hψ hψc hψs hKψ
  have hεle : (projectedExcessMeasure μ ν).real (ball (0 : Space m) (3 / 2)) ≤ e :=
    measureReal_mono (ball_subset_ball (by norm_num)) (measure_ne_top _ _)
  have hfgΔ := abs_integral_sub_mul_laplacian_le measurableSet_ball measure_ball_lt_top.ne hGm
    hf.continuous.aestronglyMeasurable
    (measurable_columnSignedHeight hS.measurableSet H).aestronglyMeasurable hfH
    (abs_columnSignedHeight_le E hH0) hfg hψ hψc hψs hMΔ
  set A := ∫ y, columnSignedHeight E H y * Δ ψ y with hA_def
  set B := ∫ y, f y * Δ ψ y with hB_def
  have h1 : |B| ≤ |A| + |B - A| := by simpa using abs_add_le A (B - A)
  have h2 : |A| ≤ Kψ * e := hgΔ.trans (mul_le_mul_of_nonneg_left hεle hKψ0)
  have h3 : 2 * H * MΔ * volume.real (ball (0 : Space m) (3 / 2) \ G) ≤
      2 * H * MΔ * (2 * 4 ^ m * e) := mul_le_mul_of_nonneg_left hGv (by positivity)
  calc |B| ≤ Kψ * e + 2 * H * MΔ * (2 * 4 ^ m * e) := by linarith
    _ = (Kψ + 2 * H * MΔ * (2 * 4 ^ m)) * e := by ring

end IsLocalPerimeterMinimizer

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **`GR11.1` for one configuration, in normalized form.** With `s = √e` and
`z_s = s⁻¹ (f - c)`, for any `z` continuous on `B̄_{1/2}`,
`∫ η (x_n - c - s ℓ)² dμ ≤ e (4 ∫ η (z - ℓ)² + 4 ∫_{B_{1/2}} (z_s - z)² + δ'² (8·4^m + 1))`. -/
theorem integral_height_sq_le_normalized (hS : SlabTrappedRepresentation b E U H H' μ ν)
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
    {a : ℝ} {p : Space m} (he : 0 < (projectedExcessMeasure μ ν).real (ball 0 2))
    (hcH : |c| + Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) * (|a| + ‖p‖) ≤ H)
    {z : Space m → ℝ} (hz : ContinuousOn z (closedBall 0 (1 / 2))) :
    ∫ x, η (horizontal x) * (x (Fin.last m) -
        (c + Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) *
          (a + inner ℝ p (horizontal x)))) ^ 2 ∂μ ≤
      (projectedExcessMeasure μ ν).real (ball 0 2) *
        (4 * (∫ y, η y * (z y - (a + inner ℝ p y)) ^ 2) +
          (4 * (∫ y in ball (0 : Space m) (1 / 2),
              ((Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)))⁻¹ * (f y - c) - z y) ^ 2) +
            (δ + Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) * (|a| + ‖p‖)) ^ 2 *
              (8 * 4 ^ m + 1))) := by
  set e := (projectedExcessMeasure μ ν).real (ball (0 : Space m) 2) with he_def
  set s := Real.sqrt e with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr he
  set zs : Space m → ℝ := fun y ↦ s⁻¹ * (f y - c) with hzs_def
  set l : Space m → ℝ := fun y ↦ a + inner ℝ p y with hl_def
  have hmain := hS.integral_height_sq_le_of_approx hU2 hf hfH hGm hGB hfE hδ hband hphase hη hηc
    hηB hη0 hη1 (a := a) (p := p) hs0.le hcH
  have hfz : ∀ y, η y * (f y - (c + s * (a + inner ℝ p y))) ^ 2 =
      e * (η y * (zs y - l y) ^ 2) := by
    intro y
    have h1 : f y - (c + s * (a + inner ℝ p y)) = s * (zs y - l y) := by
      simp only [zs, l]
      field_simp
      ring
    rw [h1, mul_pow, Real.sq_sqrt he.le]
    ring
  have hl : Continuous l := by fun_prop
  have hzsc : Continuous zs := continuous_const.mul (hf.continuous.sub continuous_const)
  have hηB' : ∀ y, y ∉ ball (0 : Space m) (1 / 2) → η y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hηB h))
  have hint_z : Integrable (fun y ↦ η y * (z y - l y) ^ 2) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      ((hη.continuous.continuousOn.mul ((hz.sub hl.continuousOn).pow 2)).integrableOn_compact
        (isCompact_closedBall 0 (1 / 2))) fun y hy ↦ ?_
    rw [hηB' y (fun h ↦ hy (ball_subset_closedBall h)), zero_mul]
  have hint_zs : Integrable (fun y ↦ η y * (zs y - l y) ^ 2) :=
    (hη.continuous.mul ((hzsc.sub hl).pow 2)).integrable_of_hasCompactSupport hηc.mul_right
  have hint_d : IntegrableOn (fun y ↦ (zs y - z y) ^ 2) (ball (0 : Space m) (1 / 2)) :=
    (((hzsc.continuousOn.sub hz).pow 2).integrableOn_compact
      (isCompact_closedBall 0 (1 / 2))).mono_set ball_subset_closedBall
  have hcmp := integral_mul_sq_le_of_approx measurableSet_ball hη0 hη1 hηB' hint_zs hint_z hint_d
  have he0 : 0 ≤ e := he.le
  calc ∫ x, η (horizontal x) * (x (Fin.last m) - (c + s * (a + inner ℝ p (horizontal x)))) ^ 2 ∂μ
      ≤ 2 * (∫ y, η y * (f y - (c + s * (a + inner ℝ p y))) ^ 2) +
          (δ + s * (|a| + ‖p‖)) ^ 2 * (8 * 4 ^ m + 1) * e := hmain
    _ = 2 * (e * ∫ y, η y * (zs y - l y) ^ 2) +
          (δ + s * (|a| + ‖p‖)) ^ 2 * (8 * 4 ^ m + 1) * e := by
        simp_rw [hfz]
        rw [integral_const_mul]
    _ ≤ 2 * (e * (2 * (∫ y, η y * (z y - l y) ^ 2) +
          2 * ∫ y in ball (0 : Space m) (1 / 2), (zs y - z y) ^ 2)) +
          (δ + s * (|a| + ‖p‖)) ^ 2 * (8 * 4 ^ m + 1) * e :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcmp he0)
          (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ = e * (4 * (∫ y, η y * (z y - l y) ^ 2) +
          (4 * (∫ y in ball (0 : Space m) (1 / 2), (zs y - z y) ^ 2) +
            (δ + s * (|a| + ‖p‖)) ^ 2 * (8 * 4 ^ m + 1))) := by ring

end SlabTrappedRepresentation

open SlabTrappedRepresentation in
/-- The bound for `∫_{B_1} z²` of the harmonic limit. -/
def gr11L2Const (m : ℕ) : ℝ := 2 * (2 ^ (m + 1) * (3 / 2) ^ 2 * gradApproxConst m)

namespace IsLocalPerimeterMinimizer

open SlabTrappedRepresentation

/-- **`GR11`: the harmonic limit of normalized heights.** Let `E_j` be local perimeter minimizers
with slab-trapped representations over `B_2 × (-H', H')` inside their domains, `0 ∈ ∂E_j`, and
excess `0 < e_j = ε_j(B_2) → 0`. Then along a subsequence:
* the normalized heights converge to a harmonic function `z` on `B_{3/2}` with
  `∫_{B_1} z² ≤ gr11L2Const m`;
* the boundary over `B_{1/2}` lies in bands `|t - c_j| ≤ δ_j` with `c_j, δ_j → 0`, outside which
  the phase is the correct half-space;
* (`GR11.1`, upper bound) for every cutoff `0 ≤ η ≤ 1` supported in `B_{1/2}`, every affine
  `ℓ = a + ⟪p, ·⟫` and every `ε > 0`, eventually
  `∫ η (x_n - c_j - √e_j ℓ)² dμ_j ≤ e_j (4 ∫ η (z - ℓ)² + ε)`. -/
theorem gr11_harmonic_limit {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {H H' : ℝ} {E Ω : ℕ → Set (Space (m + 1))} {μ : ℕ → Measure (Space (m + 1))}
    {ν : ℕ → Space (m + 1) → Space (m + 1)}
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E j) (Ω j))
    (hS : ∀ j, SlabTrappedRepresentation b (E j) (ball (0 : Space m) 2) H H' (μ j) (ν j))
    (hcyl : ∀ j, cylinderSet (ball (0 : Space m) 2) H' ⊆ Ω j)
    (h0 : ∀ j, (0 : Space (m + 1)) ∈ measureTheoreticBoundary (E j))
    (hpos : ∀ j, 0 < (projectedExcessMeasure (μ j) (ν j)).real (ball 0 2))
    (hlim : Tendsto (fun j ↦ (projectedExcessMeasure (μ j) (ν j)).real (ball 0 2)) atTop
      (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (z : Space m → ℝ) (c δ : ℕ → ℝ),
      ContDiffOn ℝ 2 z (ball 0 (3 / 2)) ∧ (∀ y ∈ ball (0 : Space m) (3 / 2), Δ z y = 0) ∧
      (∫ y in ball (0 : Space m) 1, z y ^ 2) ≤ gr11L2Const m ∧
      Tendsto c atTop (𝓝 0) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ᶠ j in atTop, ∀ x ∈ measureTheoreticBoundary (E (φ j)),
        horizontal x ∈ ball (0 : Space m) (1 / 2) → |x (Fin.last m)| < H' →
          |x (Fin.last m) - c j| ≤ δ j) ∧
      (∀ᶠ j in atTop, ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) (1 / 2) →
        |x (Fin.last m)| < H' → δ j < |x (Fin.last m) - c j| →
          (x ∈ E (φ j) ↔ c j < x (Fin.last m))) ∧
      ∀ η : Space m → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
        tsupport η ⊆ ball 0 (1 / 2) → (∀ y, 0 ≤ η y) → (∀ y, η y ≤ 1) →
        ∀ (a : ℝ) (p : Space m) (ε : ℝ), 0 < ε → ∀ᶠ j in atTop,
          ∫ x, η (horizontal x) * (x (Fin.last m) - (c j +
              Real.sqrt ((projectedExcessMeasure (μ (φ j)) (ν (φ j))).real (ball 0 2)) *
                (a + inner ℝ p (horizontal x)))) ^ 2 ∂(μ (φ j)) ≤
            (projectedExcessMeasure (μ (φ j)) (ν (φ j))).real (ball 0 2) *
              (4 * (∫ y, η y * (z y - (a + inner ℝ p y)) ^ 2) + ε) := by
  set e : ℕ → ℝ := fun j ↦ (projectedExcessMeasure (μ j) (ν j)).real (ball (0 : Space m) 2)
    with he_def
  have hH : 0 < H := (hS 0).pos
  have hHH' : H < H' := (hS 0).lt
  have hH'0 : 0 < H' := hH.trans hHH'
  have hU2 : ball (0 : Space m) 2 ⊆ ball (0 : Space m) 2 := subset_rfl
  choose G f hfL hfH hfD hrest using fun j ↦ (hS j).exists_gr9_data hU2
  set c : ℕ → ℝ := fun j ↦ ⨍ y in ball (0 : Space m) (3 / 2), f j y with hc_def
  set zs : ℕ → Space m → ℝ := fun j y ↦ (Real.sqrt (e j))⁻¹ * (f j y - c j) with hzs_def
  have hsq_pos : ∀ j, 0 < Real.sqrt (e j) := fun j ↦ Real.sqrt_pos.mpr (hpos j)
  have hzsL : ∀ j, ∃ K, LipschitzWith K (zs j) :=
    fun j ↦ ⟨_, lipschitzWith_normalized (hfL j) (c := c j) (hsq_pos j)⟩
  have hbd := fun j ↦ normalized_bounds (hfL j) (hpos j) (hfD j)
  set M := 2 ^ (m + 1) * (3 / 2) ^ 2 * gradApproxConst m + gradApproxConst m with hM_def
  have hM : ∀ j, ∫ y in ball (0 : Space m) (3 / 2), (zs j y ^ 2 + ‖fderiv ℝ (zs j) y‖ ^ 2) ≤ M := by
    intro j
    obtain ⟨K, hK⟩ := hzsL j
    have hi1 : IntegrableOn (fun y ↦ zs j y ^ 2) (ball (0 : Space m) (3 / 2)) :=
      ((hK.continuous.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 (3 / 2))).mono_set ball_subset_closedBall
    have hi2 : IntegrableOn (fun y ↦ ‖fderiv ℝ (zs j) y‖ ^ 2) (ball (0 : Space m) (3 / 2)) := by
      refine Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) measure_ball_lt_top.ne
        ((measurable_fderiv ℝ (zs j)).norm.pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun y ↦ ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hK) 2
    rw [integral_add hi1 hi2]
    exact add_le_add (hbd j).1 (hbd j).2
  have hsqrt : Tendsto (fun j ↦ Real.sqrt (e j)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at this
    exact this
  have hweak : ∀ ψ : Space m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball 0 (3 / 2) →
        Tendsto (fun j ↦ ∫ y, inner ℝ (gradient (zs j) y) (gradient ψ y)) atTop (𝓝 0) := by
    intro ψ hψ hψc hψs
    have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
    obtain ⟨Kψ, hKψ⟩ :=
      (hψ2.continuous_fderiv two_ne_zero).bounded_above_of_compact_support (hψc.fderiv ℝ)
    obtain ⟨MΔ, hMΔ⟩ := (continuous_laplacian_of_contDiff hψ2).bounded_above_of_compact_support
      (hasCompactSupport_laplacian hψc)
    set Cψ := Kψ + 2 * H * MΔ * (2 * 4 ^ m) with hCψ
    have hbound : ∀ᶠ j in atTop,
        ‖∫ y, inner ℝ (gradient (zs j) y) (gradient ψ y)‖ ≤ Cψ * Real.sqrt (e j) := by
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with j hj
      obtain ⟨hGm, -, hGv, hfg, -⟩ := hrest j hj
      have hA := (hmin j).abs_integral_approx_mul_laplacian_le (hS j) hU2 (hcyl j) (hfL j) (hfH j)
        hGm hGv hfg hψ2 hψc hψs hKψ (fun y ↦ by rw [← Real.norm_eq_abs]; exact hMΔ y)
      have h := norm_integral_inner_gradient_normalized_le (hfL j) (hfH j) (c := c j)
        (hsq_pos j) hψ2 hψc hA
      refine h.trans (le_of_eq ?_)
      rw [show (Real.sqrt (e j))⁻¹ * (Cψ * e j) = Cψ * (e j / Real.sqrt (e j)) by ring,
        Real.div_sqrt]
    have hlim' : Tendsto (fun j ↦ Cψ * Real.sqrt (e j)) atTop (𝓝 0) := by
      have := hsqrt.const_mul Cψ
      rwa [mul_zero] at this
    exact squeeze_zero_norm' hbound hlim'
  obtain ⟨φ, hφ, gℓ, -, -, hconv, hgloc, hgweak⟩ :=
    exists_subseq_tendsto_weakHarmonic (0 : Space m) (3 / 2) M zs hzsL hM hweak
  obtain ⟨z, hzC, hzΔ, hgz⟩ := weyl_lemma isOpen_ball ⟨hgloc, hgweak⟩
  have hzC2 : ContDiffOn ℝ 2 z (ball 0 (3 / 2)) := hzC.of_le (by simp)
  have hconv' : ∀ r < 3 / 2, Tendsto (fun j ↦ ∫ y in ball (0 : Space m) r,
      (zs (φ j) y - z y) ^ 2) atTop (𝓝 0) := by
    intro r hr
    refine (hconv r hr).congr' (Eventually.of_forall fun j ↦ integral_congr_ae ?_)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hr.le) hgz] with y hy
    rw [hy]
  -- the `L²` bound of the limit
  have hz1 : ContinuousOn z (closedBall 0 1) :=
    hzC.continuousOn.mono (closedBall_subset_ball (by norm_num))
  have hL2 : (∫ y in ball (0 : Space m) 1, z y ^ 2) ≤ gr11L2Const m := by
    have hzi : IntegrableOn (fun y ↦ z y ^ 2) (ball (0 : Space m) 1) :=
      ((hz1.pow 2).integrableOn_compact (isCompact_closedBall 0 1)).mono_set
        ball_subset_closedBall
    have hu : ∀ j, IntegrableOn (fun y ↦ zs (φ j) y ^ 2) (ball (0 : Space m) 1) := fun j ↦ by
      obtain ⟨K, hK⟩ := hzsL (φ j)
      exact ((hK.continuous.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
    have huz : ∀ j, IntegrableOn (fun y ↦ (zs (φ j) y - z y) ^ 2) (ball (0 : Space m) 1) :=
      fun j ↦ by
        obtain ⟨K, hK⟩ := hzsL (φ j)
        exact (((hK.continuous.continuousOn.sub hz1).pow 2).integrableOn_compact
          (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
    have hA : ∀ j, ∫ y in ball (0 : Space m) 1, zs (φ j) y ^ 2 ≤
        2 ^ (m + 1) * (3 / 2) ^ 2 * gradApproxConst m := fun j ↦ by
      obtain ⟨K, hK⟩ := hzsL (φ j)
      refine (setIntegral_mono_set (((hK.continuous.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 (3 / 2))).mono_set ball_subset_closedBall)
        (Eventually.of_forall fun _ ↦ sq_nonneg _)
        (Eventually.of_forall (ball_subset_ball (by norm_num)))).trans ?_
      exact (hbd (φ j)).1
    have h := integral_sq_le_of_tendsto hzi hu huz hA (hconv' 1 (by norm_num))
    rw [gr11L2Const]
    exact h
  -- the bands
  set r₀ : ℝ := min (1 / 4) ((H' - H) / 2) with hr₀_def
  have hr₀ : 0 < r₀ := lt_min (by norm_num) (by linarith)
  have hc0 := minimizerVolumeDensityConst_pos m
  have helim : Tendsto (fun j ↦ e (φ j)) atTop (𝓝 0) := hlim.comp hφ.tendsto_atTop
  have hsqrtφ : Tendsto (fun j ↦ Real.sqrt (e (φ j))) atTop (𝓝 0) := hsqrt.comp hφ.tendsto_atTop
  have hSlim : Tendsto (fun j ↦ gr11BandConst m H * Real.sqrt (e (φ j)) + 2 * H' * e (φ j))
      atTop (𝓝 0) := by
    have := (hsqrtφ.const_mul (gr11BandConst m H)).add (helim.const_mul (2 * H'))
    rwa [mul_zero, mul_zero, add_zero] at this
  have hev_small : ∀ᶠ j in atTop, e (φ j) ≤ 1 / 2 ∧
      gr11BandConst m H * Real.sqrt (e (φ j)) + 2 * H' * e (φ j) <
        minimizerVolumeDensityConst m * r₀ ^ (m + 1) :=
    (helim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
      (hSlim.eventually (gt_mem_nhds
        (show (0 : ℝ) < minimizerVolumeDensityConst m * r₀ ^ (m + 1) by positivity)))
  set δ : ℕ → ℝ := fun j ↦ gr11BandWidth m H H' (e (φ j)) with hδ_def
  set c' : ℕ → ℝ := fun j ↦ c (φ j) with hc'_def
  have hband_ev : ∀ᶠ j in atTop,
      |c' j| ≤ H ∧
      (∀ x ∈ measureTheoreticBoundary (E (φ j)), horizontal x ∈ ball (0 : Space m) (1 / 2) →
        |x (Fin.last m)| < H' → |x (Fin.last m) - c' j| ≤ δ j) ∧
      (∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) (1 / 2) → |x (Fin.last m)| < H' →
        δ j < |x (Fin.last m) - c' j| → (x ∈ E (φ j) ↔ c' j < x (Fin.last m))) := by
    filter_upwards [hev_small] with j hj
    obtain ⟨hGm, -, hGv, hfg, -⟩ := hrest (φ j) hj.1
    exact (hmin (φ j)).band_of_approx (hS (φ j)) hU2 (hcyl (φ j)) (hfL (φ j)) (hfH (φ j)) hGm
      hGv hfg (hfD (φ j)) (hj.1.trans (by norm_num)) hr₀ (min_le_left _ _) (min_le_right _ _)
      hj.2
  have hδlim : Tendsto δ atTop (𝓝 0) := (tendsto_gr11BandWidth m H H').comp helim
  have hc'lim : Tendsto c' atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hδlim
    filter_upwards [hband_ev] with j hj
    have h := hj.2.1 0 (h0 (φ j)) (by rw [horizontal_zero]; exact mem_ball_self (by norm_num))
      (by simp [hH'0])
    rw [Real.norm_eq_abs]
    simpa using h
  refine ⟨φ, hφ, z, c', δ, hzC2, fun y hy ↦ hzΔ y hy, hL2, hc'lim, hδlim,
    hband_ev.mono fun j hj ↦ hj.2.1, hband_ev.mono fun j hj ↦ hj.2.2, ?_⟩
  -- `GR11.1`
  intro η hη hηc hηB hη0 hη1 a p ε hε
  have hzc : ContinuousOn z (closedBall 0 (1 / 2)) :=
    hzC.continuousOn.mono (closedBall_subset_ball (by norm_num))
  have hT : Tendsto (fun j ↦ 4 * (∫ y in ball (0 : Space m) (1 / 2), (zs (φ j) y - z y) ^ 2) +
      (δ j + Real.sqrt (e (φ j)) * (|a| + ‖p‖)) ^ 2 * (8 * 4 ^ m + 1)) atTop (𝓝 0) := by
    have := ((hconv' (1 / 2) (by norm_num)).const_mul 4).add
      (((hδlim.add (hsqrtφ.mul_const (|a| + ‖p‖))).pow 2).mul_const (8 * 4 ^ m + 1))
    simpa using this
  have hTH : Tendsto (fun j ↦ |c' j| + Real.sqrt (e (φ j)) * (|a| + ‖p‖)) atTop (𝓝 0) := by
    have := hc'lim.abs.add (hsqrtφ.mul_const (|a| + ‖p‖))
    simpa using this
  filter_upwards [hband_ev, hev_small, hT.eventually (gt_mem_nhds hε),
    hTH.eventually (ge_mem_nhds hH)] with j hjb hjs hjT hjH
  obtain ⟨hGm, -, hGv, -, hfE⟩ := hrest (φ j) hjs.1
  have hδ0 : 0 ≤ δ j := gr11BandWidth_nonneg m hH.le hH'0.le (hpos _).le
  have h := (hS (φ j)).integral_height_sq_le_normalized hU2 (hfL (φ j)) (hfH (φ j)) hGm hGv hfE
    hδ0 hjb.2.1 hjb.2.2 hη hηc hηB hη0 hη1 (a := a) (p := p) (hpos (φ j)) hjH hzc
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (hpos (φ j)).le)
  exact add_le_add le_rfl hjT.le

end IsLocalPerimeterMinimizer

end SerrinEpigraph
