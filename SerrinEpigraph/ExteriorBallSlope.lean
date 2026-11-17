module

public import SerrinEpigraph.MicroscopicWeiss
public import SerrinEpigraph.HarmonicOneDimensionalLimit
public import SerrinEpigraph.PlaneTiltRotation
public import SerrinEpigraph.Barrier

/-!
# Exact Normal Slope at an Exterior Zero Ball and Annular Hopf Exclusion

This module formalizes sections TB5, TB6, and TB7 of
`docs/rigidity-proof/tangent-ball-comparison.md`:

1. **Exterior zero-ball halfspace support and linear upper bound (TB5.1)**:
   If `V` vanishes on an exterior ball `ball (-(R • ν)) R` (`‖ν‖ = 1`, `0 < R`), every
   microscopic blowup `W_lim` at `0` vanishes on `{x | inner ℝ ν x ≤ 0}` and satisfies
   `0 ≤ W_lim x ≤ κ * max (inner ℝ ν x) 0`.
2. **Coordinate-free Euclidean Picone classification (TB5.2–TB5.4)**:
   Any nontrivial 1-homogeneous nonnegative `κ`-Lipschitz function `W_lim` vanishing on
   `{x | inner ℝ ν x ≤ 0}` and satisfying truncated harmonicity has the halfspace linear form
   `W_lim x = c * max (inner ℝ ν x) 0` for a constant `c ∈ Ioc 0 κ`.
3. **Stress-stationarity identification of the slope `c = κ` and full-family normal slope (TB6)**:
   Passing rescaled spatial stress stationarity to the microscopic blowup limit against a compactly
   supported constant-direction vector field `φ(x) • ν` identifies `c² = 2 * normalizedPotential f 0 = κ²`,
   forcing `c = κ` for every convergent blowup subsequence and hence full-family normal slope
   `V (s • ν) / s → κ` as `s → 0⁺`.
4. **Weak annular Hopf comparison excluding opposite phase balls with strict difference (TB7)**:
   When `V ≤ V_tilde` are physical translation limits vanishing at `0` such that `V` has an
   exterior zero ball `ball (-(r • ν)) r`, `V_tilde` is positive on the interior tangent ball
   `ball (r • ν) r`, and `V < V_tilde` on `ball (r • ν) r`, testing the weak inequality for
   `V_tilde - V - ε • annularBarrier (r • ν) α r + δ` against its Lipschitz negative part forces a
   strictly positive inward normal slope gap `(V_tilde (s • ν) - V (s • ν)) / s ≥ b_* > 0`,
   contradicting `V_tilde (s • ν) ≤ κ * s` and `V (s • ν) / s → κ`.
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal NNReal Laplacian

namespace SerrinEpigraph

/-! ### Measure-zero hyperplanes and Euler's identity for 1-homogeneous Lipschitz functions -/

/-- Any orthogonal hyperplane `{x | inner ℝ ν x = 0}` of a unit vector `ν` has Lebesgue measure
zero. -/
theorem measure_orthogonal_hyperplane_eq_zero {d : ℕ} {ν : Space d} (hν : ‖ν‖ = 1) :
    volume {x : Space d | inner ℝ ν x = 0} = 0 := by
  let S : Submodule ℝ (Space d) := LinearMap.ker (innerₛₗ ℝ ν)
  have hne : S ≠ ⊤ := by
    intro htop
    have hmem : ν ∈ S := htop ▸ Submodule.mem_top
    have h0 : inner ℝ ν ν = 0 := hmem
    rw [real_inner_self_eq_norm_sq, hν] at h0
    norm_num at h0
  change volume (S : Set (Space d)) = 0
  exact Measure.addHaar_submodule volume S hne

/-- Almost-everywhere differentiability of a globally Lipschitz function on `Space d`. -/
private theorem ae_differentiableAt_lipschitz {d : ℕ} {v : Space d → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) : ∀ᵐ x, DifferentiableAt ℝ v x := by
  have he (n : ℕ) : ∀ᵐ x, x ∈ closedBall (0 : Space d) (n + 1) →
      DifferentiableWithinAt ℝ v (closedBall 0 (n + 1)) x :=
    (hv.lipschitzOnWith (s := closedBall 0 (n + 1))).ae_differentiableWithinAt_of_mem
  filter_upwards [ae_all_iff.mpr he] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  have hb : x ∈ ball (0 : Space d) (n + 1) := by
    simp only [mem_ball, dist_zero_right]; linarith
  exact (hx n (ball_subset_closedBall hb)).differentiableAt (closedBall_mem_nhds_of_mem hb)

/-- Euler's homogeneous function theorem at any differentiability point of a positively
1-homogeneous scalar function. -/
theorem euler_oneHomogeneous_inner_gradient {d : ℕ} {W : Space d → ℝ}
    (hW_homog : ∀ t : ℝ, 0 ≤ t → ∀ x, W (t • x) = t * W x)
    {x : Space d} (hd : DifferentiableAt ℝ W x) :
    inner ℝ (gradient W x) x = W x := by
  have h1 : HasDerivAt (fun t : ℝ ↦ W (t • x)) (inner ℝ (gradient W x) x) 1 := by
    have hsmul : HasDerivAt (fun t : ℝ ↦ t • x) x 1 :=
      ((hasDerivAt_id (1 : ℝ)).smul_const x).congr_deriv (one_smul ℝ x)
    have hW1 : DifferentiableAt ℝ W ((1 : ℝ) • x) := by rwa [one_smul]
    have hcomp : HasDerivAt (fun t : ℝ ↦ W (t • x)) (fderiv ℝ W ((1 : ℝ) • x) x) 1 :=
      hW1.hasFDerivAt.comp_hasDerivAt 1 hsmul
    exact hcomp.congr_deriv (by rw [one_smul, inner_gradient_left])
  have h2 : HasDerivAt (fun t : ℝ ↦ t * W x) (W x) 1 :=
    ((hasDerivAt_id (1 : ℝ)).mul_const (W x)).congr_deriv (one_mul (W x))
  have hev : (fun t : ℝ ↦ W (t • x)) =ᶠ[𝓝 1] (fun t : ℝ ↦ t * W x) := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht
    exact hW_homog t (le_of_lt ht) x
  exact h1.unique (h2.congr_of_eventuallyEq hev)

/-! ### TB5.1: Exterior zero-ball vanishing on the nonpositive halfspace -/

/-- Points strictly in the negative halfspace `{x | inner ℝ ν x < 0}` eventually fall inside the
rescaled exterior zero ball `(r_seq j)⁻¹ • ball (-(R • ν)) R` as `r_seq j → 0⁺`. -/
theorem eventually_smul_mem_exterior_ball {d : ℕ} {ν x : Space d} {R : ℝ}
    {r_seq : ℕ → ℝ} (hν : ‖ν‖ = 1) (hR : 0 < R)
    (hr_pos : ∀ j, 0 < r_seq j) (hr_lim : Tendsto r_seq atTop (𝓝 0))
    (hx : inner ℝ ν x < 0) :
    ∀ᶠ j in atTop, r_seq j • x ∈ ball (-(R • ν)) R := by
  have hpos : 0 < -2 * R * inner ℝ ν x := by nlinarith
  have ht : Tendsto (fun j ↦ r_seq j * ‖x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [zero_mul] using hr_lim.mul_const (‖x‖ ^ 2)
  filter_upwards [ht.eventually (gt_mem_nhds hpos)] with j hj
  rw [mem_ball, dist_eq_norm, sub_neg_eq_add]
  have hsq : ‖r_seq j • x + R • ν‖ ^ 2 < R ^ 2 := by
    have hexp : ‖r_seq j • x + R • ν‖ ^ 2 =
        (r_seq j) ^ 2 * ‖x‖ ^ 2 + 2 * R * r_seq j * inner ℝ ν x + R ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, hν]
      rw [abs_of_pos (hr_pos j), abs_of_pos hR, real_inner_comm x ν]
      ring
    rw [hexp]
    have hrj := hr_pos j
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hR.le hsq

/-- Any microscopic blowup at `0` of a function vanishing on `ball (-(R • ν)) R` vanishes on the
entire closed nonpositive halfspace `{x | inner ℝ ν x ≤ 0}`. -/
theorem microscopic_blowup_zero_on_nonpos_halfspace {d : ℕ} {V W_lim : Space d → ℝ}
    {ν : Space d} {R : ℝ} {r_seq : ℕ → ℝ}
    (hν : ‖ν‖ = 1) (hR : 0 < R) (hzero_ball : ball (-(R • ν)) R ⊆ {x | V x = 0})
    (hr_pos : ∀ j, 0 < r_seq j) (hr_lim : Tendsto r_seq atTop (𝓝 0))
    (hW_cont : Continuous W_lim)
    (hWlim : ∀ K : Set (Space d), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ V (r_seq j • x) / r_seq j) W_lim atTop K) :
    ∀ x, inner ℝ ν x ≤ 0 → W_lim x = 0 := by
  have hneg : ∀ y : Space d, inner ℝ ν y < 0 → W_lim y = 0 := by
    intro y hy
    have hpt : Tendsto (fun j ↦ V (r_seq j • y) / r_seq j) atTop (𝓝 (W_lim y)) :=
      (hWlim {y} isCompact_singleton).tendsto_at (mem_singleton y)
    have hev : ∀ᶠ j in atTop, V (r_seq j • y) / r_seq j = 0 := by
      filter_upwards [eventually_smul_mem_exterior_ball hν hR hr_pos hr_lim hy] with j hj
      have hV0 : V (r_seq j • y) = 0 := hzero_ball hj
      rw [hV0, zero_div]
    exact tendsto_nhds_unique hpt (tendsto_const_nhds.congr' (hev.mono fun _ hj ↦ hj.symm))
  intro x hx
  have hseq : Tendsto (fun k : ℕ ↦ x - (1 / ((k : ℝ) + 1)) • ν) atTop (𝓝 x) := by
    have ht0 : Tendsto (fun k : ℕ ↦ (1 / ((k : ℝ) + 1)) • ν) atTop (𝓝 ((0 : ℝ) • ν)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.smul_const ν
    rw [zero_smul] at ht0
    simpa only [sub_zero] using tendsto_const_nhds.sub ht0
  have hval (k : ℕ) : W_lim (x - (1 / ((k : ℝ) + 1)) • ν) = 0 := by
    apply hneg
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hν]
    have hk : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  exact tendsto_nhds_unique ((hW_cont.tendsto x).comp hseq)
    (tendsto_const_nhds.congr (fun k ↦ (hval k).symm))

/-- A nonnegative `κ`-Lipschitz function vanishing on `{x | inner ℝ ν x ≤ 0}` (`‖ν‖ = 1`) is
bounded above by `κ * max (inner ℝ ν x) 0`. -/
theorem lipschitz_le_linear_pos_of_zero_on_nonpos_halfspace {d : ℕ} {W : Space d → ℝ}
    {ν : Space d} {κ : ℝ} (hκ : 0 < κ) (hν : ‖ν‖ = 1)
    (hW : LipschitzWith ⟨κ, hκ.le⟩ W)
    (hzero : ∀ x, inner ℝ ν x ≤ 0 → W x = 0) (x : Space d) :
    W x ≤ κ * max (inner ℝ ν x) 0 := by
  by_cases hx : inner ℝ ν x ≤ 0
  · rw [hzero x hx, max_eq_right hx, mul_zero]
  · push Not at hx
    let y : Space d := x - (inner ℝ ν x) • ν
    have hy : inner ℝ ν y ≤ 0 := by
      dsimp only [y]
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hν]
      linarith
    have hd := hW.dist_le_mul x y
    rw [hzero y hy, Real.dist_eq, sub_zero, dist_eq_norm] at hd
    have hxy : x - y = (inner ℝ ν x) • ν := by dsimp only [y]; abel
    rw [hxy, norm_smul, hν, mul_one, Real.norm_of_nonneg hx.le] at hd
    rw [max_eq_left hx.le]
    exact (le_abs_self (W x)).trans hd

/-! ### TB5.2–TB5.4: Pure Euclidean Picone classification of 1-homogeneous halfspace blowups -/

/-- Product of locally Lipschitz scalar functions on `Space d`. -/
private theorem locallyLipschitz_mul_space {d : ℕ} {f g : Space d → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x ↦ f x * g x) := by
  have hm : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦ z.1 * z.2) := by fun_prop
  exact hm.locallyLipschitz.comp (hf.prodMk hg)

/-- Positive part of a locally Lipschitz scalar function on `Space d` is locally Lipschitz. -/
private theorem locallyLipschitz_posPart {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) : LocallyLipschitz (fun x ↦ max (v x) 0) := by
  have hmax : LipschitzWith 1 (fun t : ℝ ↦ max t 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
    exact abs_max_sub_max_le_abs a b 0
  exact hmax.locallyLipschitz.comp hv

/-- Local Lipschitz regularity of the localized Picone quotient
`θ x * (W x ^ 2 * (max (inner ℝ ν x) 0 + ε)⁻¹)`. -/
private theorem piconeQuotient_locallyLipschitz {d : ℕ} {W : Space d → ℝ} {ν : Space d}
    {κ ε : ℝ} (hκ : 0 < κ) (hν : ‖ν‖ = 1) (hε : 0 < ε)
    (hW : LipschitzWith ⟨κ, hκ.le⟩ W) (θ : ContDiffBump (0 : Space d)) :
    LocallyLipschitz (fun x ↦ (θ : Space d → ℝ) x *
      (W x ^ 2 / (max (inner ℝ ν x) 0 + ε))) := by
  have hθ : LocallyLipschitz (θ : Space d → ℝ) := (θ.contDiff (n := 1)).locallyLipschitz
  have hWsq : LocallyLipschitz (fun x ↦ W x ^ 2) := by
    simpa only [sq] using locallyLipschitz_mul_space hW.locallyLipschitz hW.locallyLipschitz
  have hD_lip : LipschitzWith 1 (fun x : Space d ↦ max (inner ℝ ν x) 0 + ε) := by
    have hin : LipschitzWith 1 (fun x : Space d ↦ inner ℝ ν x) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [NNReal.coe_one, one_mul, Real.dist_eq, ← inner_sub_right, dist_eq_norm]
      exact (abs_real_inner_le_norm ν (x - y)).trans (by rw [hν, one_mul])
    have hm : LipschitzWith 1 (fun x : Space d ↦ max (inner ℝ ν x) 0) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [NNReal.coe_one, one_mul, Real.dist_eq]
      exact (abs_max_sub_max_le_abs _ _ 0).trans (by
        simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using hin.dist_le_mul x y)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using hm.dist_le_mul x y
  have hinv_lip : LipschitzWith ⟨(ε ^ 2)⁻¹, inv_nonneg.mpr (sq_nonneg ε)⟩
      (fun t : ℝ ↦ (max t ε)⁻¹) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have ha : ε ≤ max a ε := le_max_right a ε
    have hb : ε ≤ max b ε := le_max_right b ε
    have ha0 : 0 < max a ε := hε.trans_le ha
    have hb0 : 0 < max b ε := hε.trans_le hb
    change |(max a ε)⁻¹ - (max b ε)⁻¹| ≤ (ε ^ 2)⁻¹ * |a - b|
    have hdiff : |(max a ε)⁻¹ - (max b ε)⁻¹| = |max b ε - max a ε| / (max a ε * max b ε) := by
      rw [inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_of_pos (mul_pos ha0 hb0)]
    have hmax_le : |max b ε - max a ε| ≤ |a - b| := by
      rw [abs_sub_comm (max b ε)]
      exact abs_max_sub_max_le_abs a b ε
    rw [hdiff]
    calc
      |max b ε - max a ε| / (max a ε * max b ε) ≤ |a - b| / (max a ε * max b ε) :=
        div_le_div_of_nonneg_right hmax_le (mul_nonneg ha0.le hb0.le)
      _ ≤ |a - b| / ε ^ 2 := by
        apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hε)
        rw [sq]
        exact mul_le_mul ha hb hε.le ha0.le
      _ = (ε ^ 2)⁻¹ * |a - b| := by ring
  have hinv : LocallyLipschitz (fun x : Space d ↦ (max (inner ℝ ν x) 0 + ε)⁻¹) := by
    have hc := (hinv_lip.comp hD_lip).locallyLipschitz
    convert hc using 1
    funext x
    dsimp only [Function.comp_apply]
    congr 1
    exact (max_eq_left (le_add_of_nonneg_left (le_max_right _ _))).symm
  have htot := locallyLipschitz_mul_space hθ (locallyLipschitz_mul_space hWsq hinv)
  simpa only [div_eq_mul_inv] using htot

/-- Derivative of a radial bump `x ↦ χ₁ (‖x‖ ^ 2)` on `Space d`. -/
private theorem hasFDerivAt_radialNormSq {d : ℕ} {χ₁ : ℝ → ℝ}
    (hχ₁ : ContDiff ℝ 1 χ₁) (x : Space d) :
    HasFDerivAt (fun y : Space d ↦ χ₁ (‖y‖ ^ 2))
      ((2 * deriv χ₁ (‖x‖ ^ 2)) • (toDual ℝ (Space d) x)) x := by
  have hnsq : HasFDerivAt (fun y : Space d ↦ ‖y‖ ^ 2)
      ((2 : ℝ) • (toDual ℝ (Space d) x)) x := by
    have heq : (fun y : Space d ↦ ‖y‖ ^ 2) = fun y ↦ inner ℝ y y := by
      funext y; exact (real_inner_self_eq_norm_sq y).symm
    rw [heq]
    refine ((hasFDerivAt_id x).inner ℝ (hasFDerivAt_id x)).congr_fderiv ?_
    ext v
    simp only [fderivInnerCLM_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, smul_apply,
      toDual_apply_apply, id_eq]
    rw [real_inner_comm v x]
    ring
  have hd : HasDerivAt χ₁ (deriv χ₁ (‖x‖ ^ 2)) (‖x‖ ^ 2) :=
    (hχ₁.differentiable one_ne_zero (‖x‖ ^ 2)).hasDerivAt
  refine (hd.comp_hasFDerivAt x hnsq).congr_fderiv ?_
  ext v
  simp only [smul_apply, toDual_apply_apply, smul_eq_mul]
  ring

/-- Gradient of `x ↦ χ₁ (‖x‖ ^ 2)`. -/
private theorem gradient_radialNormSq {d : ℕ} {χ₁ : ℝ → ℝ}
    (hχ₁ : ContDiff ℝ 1 χ₁) (x : Space d) :
    gradient (fun y : Space d ↦ χ₁ (‖y‖ ^ 2)) x = (2 * deriv χ₁ (‖x‖ ^ 2)) • x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, (hasFDerivAt_radialNormSq hχ₁ x).fderiv,
    smul_apply, toDual_apply_apply, real_inner_smul_left, smul_eq_mul]

/-- **Coordinate-free Euclidean Picone classification (TB5.2–TB5.4)**:
Every nontrivial 1-homogeneous nonnegative `κ`-Lipschitz function vanishing on
`{x | inner ℝ ν x ≤ 0}` and satisfying truncated harmonicity on `Space (m + 1)` has the exact
halfspace linear form `W_lim x = c * max (inner ℝ ν x) 0` for a constant `c ∈ Ioc 0 κ`. -/
theorem halfspace_oneHomogeneous_eq_linear_pos {m : ℕ} {W_lim : Space (m + 1) → ℝ}
    {ν : Space (m + 1)} {κ : ℝ} (hκ : 0 < κ) (hν : ‖ν‖ = 1)
    (hW : LipschitzWith ⟨κ, hκ.le⟩ W_lim) (hW0 : ∀ x, 0 ≤ W_lim x)
    (hW_zero_half : ∀ x, inner ℝ ν x ≤ 0 → W_lim x = 0)
    (hW_homog : ∀ t : ℝ, 0 ≤ t → ∀ x, W_lim (t • x) = t * W_lim x)
    (hnondeg : ∃ x ∈ closedBall 0 1, 0 < W_lim x)
    (htrunc : ∀ η : Space (m + 1) → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, η x * ‖gradient W_lim x‖ ^ 2 +
        W_lim x * inner ℝ (gradient W_lim x) (gradient η x)) = 0) :
    ∃ c ∈ Ioc 0 κ, ∀ x, W_lim x = c * max (inner ℝ ν x) 0 := by
  have hW_zero : W_lim 0 = 0 := by
    apply hW_zero_half 0
    simp
  have hW_le := lipschitz_le_linear_pos_of_zero_on_nonpos_halfspace hκ hν hW hW_zero_half
  have hW_grad_le (x : Space (m + 1)) : ‖gradient W_lim x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hW
  have hnull_hyp : ∀ᵐ x, inner ℝ ν x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using measure_orthogonal_hyperplane_eq_zero hν
  -- Step 1: On every compact slab `closedBall 0 R_B ∩ {x | δ ≤ inner ℝ ν x}`, the Picone
  -- remainder `‖gradient W_lim x - (W_lim x / inner ℝ ν x) • ν‖ ^ 2` integrates to zero.
  have hslab_zero (R_B δ : ℝ) (hR_B : 0 < R_B) (hδ : 0 < δ) :
      (∫ x in closedBall 0 R_B ∩ {x | δ ≤ inner ℝ ν x},
        ‖gradient W_lim x - (W_lim x / inner ℝ ν x) • ν‖ ^ 2) = 0 := by
    let χ₁ : ContDiffBump (0 : ℝ) :=
      { rIn := R_B ^ 2
        rOut := R_B ^ 2 + 1
        rIn_pos := sq_pos_of_pos hR_B
        rIn_lt_rOut := lt_add_one _ }
    let ψ : Space (m + 1) → ℝ := fun x ↦ χ₁ (‖x‖ ^ 2)
    have hχ₁_cd : ContDiff ℝ 1 (χ₁ : ℝ → ℝ) := χ₁.contDiff
    have hψ : ContDiff ℝ 1 ψ := hχ₁_cd.comp ((contDiff_id (𝕜 := ℝ)).norm_sq ℝ)
    let L_ball : Set (Space (m + 1)) := closedBall 0 (R_B + 2)
    have hL_comp : IsCompact L_ball := isCompact_closedBall 0 (R_B + 2)
    have hψ_supp : tsupport ψ ⊆ closedBall 0 (R_B + 1) := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      rw [Function.mem_support] at hx
      rw [mem_closedBall, dist_zero_right]
      by_contra hgt
      push Not at hgt
      have hsq : R_B ^ 2 + 1 < ‖x‖ ^ 2 := by nlinarith
      have hout : ‖x‖ ^ 2 ∉ ball (0 : ℝ) χ₁.rOut := by
        simp only [χ₁, mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg ‖x‖), not_lt]
        exact hsq.le
      have hχ0 : (χ₁ : ℝ → ℝ) (‖x‖ ^ 2) = 0 :=
        Function.notMem_support.mp (by rwa [χ₁.support_eq])
      exact hx hχ0
    have hψ_L : tsupport ψ ⊆ L_ball :=
      hψ_supp.trans (closedBall_subset_closedBall (by linarith))
    have hcψ : HasCompactSupport ψ :=
      (isCompact_closedBall 0 (R_B + 1)).of_isClosed_subset (isClosed_tsupport ψ) hψ_supp
    have hψ_one (x : Space (m + 1)) (hx : x ∈ closedBall 0 R_B) : ψ x = 1 := by
      have hnx : ‖x‖ ≤ R_B := by simpa only [mem_closedBall, dist_zero_right] using hx
      apply χ₁.one_of_mem_closedBall
      simp only [χ₁, mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg ‖x‖)]
      exact pow_le_pow_left₀ (norm_nonneg x) hnx 2
    -- Truncated harmonicity identity with `η = ψ` and Euler 1-homogeneity
    have htrunc_ψ : (∫ x in L_ball, ψ x * ‖gradient W_lim x‖ ^ 2) =
        -∫ x in L_ball, 2 * deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2) * W_lim x ^ 2 := by
      have hi1_on : IntegrableOn (fun x ↦ ψ x * ‖gradient W_lim x‖ ^ 2) (tsupport ψ) := by
        apply ((continuousOn_const (s := tsupport ψ) (c := κ ^ 2)).integrableOn_compact hcψ).mono'
          (hψ.continuous.measurable.mul
            ((measurable_gradient W_lim).norm.pow_const 2)).aestronglyMeasurable
        filter_upwards with x
        dsimp only [Pi.mul_apply]
        rw [norm_mul, Real.norm_of_nonneg χ₁.nonneg, Real.norm_of_nonneg (sq_nonneg _)]
        simpa only [one_mul] using
          mul_le_mul χ₁.le_one (pow_le_pow_left₀ (norm_nonneg _) (hW_grad_le x) 2)
            (sq_nonneg _) zero_le_one
      have hi1 : Integrable (fun x ↦ ψ x * ‖gradient W_lim x‖ ^ 2) :=
        hi1_on.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
          simp [image_eq_zero_of_notMem_tsupport hx])
      have hi2_on : IntegrableOn
          (fun x ↦ W_lim x * inner ℝ (gradient W_lim x) (gradient ψ x)) (tsupport ψ) := by
        obtain ⟨Cg, hCg⟩ := gradient_bound_of_locallyLipschitz hψ.locallyLipschitz hcψ
        apply (continuousOn_const.integrableOn_compact hcψ
          (f := fun _ ↦ κ * (R_B + 1) * (κ * Cg))).mono'
          (hW.continuous.measurable.mul
            ((measurable_gradient W_lim).inner (𝕜 := ℝ)
              (measurable_gradient ψ))).aestronglyMeasurable
        filter_upwards [ae_restrict_mem hcψ.measurableSet] with x hx
        have hnx : ‖x‖ ≤ R_B + 1 := by
          simpa only [mem_closedBall, dist_zero_right] using hψ_supp hx
        have hWx : ‖W_lim x‖ ≤ κ * (R_B + 1) := by
          have hd := hW.dist_le_mul x 0
          rw [hW_zero, dist_zero_right, dist_zero_right] at hd
          exact hd.trans (mul_le_mul_of_nonneg_left hnx hκ.le)
        dsimp only [Pi.mul_apply]
        rw [norm_mul]
        exact mul_le_mul hWx ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hW_grad_le x) (hCg x hx) (norm_nonneg _) hκ.le))
          (norm_nonneg _) (by positivity)
      have hi2 : Integrable (fun x ↦ W_lim x * inner ℝ (gradient W_lim x) (gradient ψ x)) :=
        hi2_on.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
          simp [gradient, fderiv_of_notMem_tsupport ℝ hx])
      have htot := htrunc ψ hψ hcψ
      rw [integral_add hi1 hi2] at htot
      have hL1 : (∫ x in L_ball, ψ x * ‖gradient W_lim x‖ ^ 2) =
          ∫ x, ψ x * ‖gradient W_lim x‖ ^ 2 :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
          simp [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hψ_L hh))])
      have hL2 : (∫ x, W_lim x * inner ℝ (gradient W_lim x) (gradient ψ x)) =
          ∫ x in L_ball, 2 * deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2) * W_lim x ^ 2 := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
          have hn : x ∉ tsupport ψ := fun hh ↦ hx (hψ_L hh)
          simp [gradient, fderiv_of_notMem_tsupport ℝ hn])]
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (ae_differentiableAt_lipschitz hW)] with x hdx
        rw [gradient_radialNormSq hχ₁_cd x, real_inner_smul_right,
          euler_oneHomogeneous_inner_gradient hW_homog hdx]
        ring
      rw [hL1, ← hL2]
      linarith
    -- Picone identity at positive regularization `ε > 0`
    let θ : ContDiffBump (0 : Space (m + 1)) :=
      { rIn := R_B + 3
        rOut := R_B + 4
        rIn_pos := by positivity
        rIn_lt_rOut := by linarith }
    have hpicone_eps (ε : ℝ) (hε : 0 < ε) :
        (∫ x in L_ball, ψ x *
          ‖gradient W_lim x - (W_lim x / (max (inner ℝ ν x) 0 + ε)) • ν‖ ^ 2) =
        -∫ x in L_ball, 2 * deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2) *
          (ε / (max (inner ℝ ν x) 0 + ε)) * W_lim x ^ 2 := by
      let uε : Space (m + 1) → ℝ :=
        fun x ↦ (θ : Space (m + 1) → ℝ) x * (W_lim x ^ 2 / (max (inner ℝ ν x) 0 + ε))
      have huε_lip : LocallyLipschitz uε :=
        piconeQuotient_locallyLipschitz hκ hν hε hW θ
      have huε_val (x : Space (m + 1)) : uε x ∈ Icc 0 ((κ * (R_B + 4)) ^ 2 / ε) := by
        have hden : 0 < max (inner ℝ ν x) 0 + ε :=
          add_pos_of_nonneg_of_pos (le_max_right _ _) hε
        refine ⟨mul_nonneg θ.nonneg (div_nonneg (sq_nonneg _) hden.le), ?_⟩
        by_cases hx_in : x ∈ ball (0 : Space (m + 1)) θ.rOut
        · have hnx : ‖x‖ ≤ R_B + 4 := by
            have hlt : ‖x‖ < R_B + 4 := by simpa only [θ, mem_ball, dist_zero_right] using hx_in
            exact hlt.le
          have hWx : W_lim x ≤ κ * (R_B + 4) := by
            have hd := hW.dist_le_mul x 0
            rw [hW_zero, Real.dist_eq, sub_zero, dist_zero_right] at hd
            exact (le_abs_self _).trans (hd.trans (mul_le_mul_of_nonneg_left hnx hκ.le))
          have hsq_le : W_lim x ^ 2 ≤ (κ * (R_B + 4)) ^ 2 :=
            pow_le_pow_left₀ (hW0 x) hWx 2
          calc
            uε x ≤ 1 * (W_lim x ^ 2 / (max (inner ℝ ν x) 0 + ε)) :=
              mul_le_mul_of_nonneg_right θ.le_one (div_nonneg (sq_nonneg _) hden.le)
            _ ≤ (κ * (R_B + 4)) ^ 2 / ε := by
              rw [one_mul]
              exact (div_le_div_of_nonneg_left (sq_nonneg _) hε
                (le_add_of_nonneg_left (le_max_right _ _))).trans
                (div_le_div_of_nonneg_right hsq_le hε.le)
        · have hθ0 : (θ : Space (m + 1) → ℝ) x = 0 :=
            Function.notMem_support.mp (by rwa [θ.support_eq])
          dsimp only [uε]
          rw [hθ0, zero_mul]
          exact div_nonneg (sq_nonneg _) hε.le
      have hibp := setIntegral_inner_gradient_mul_eq_neg_of_locallyLipschitz
        huε_lip huε_val hψ hcψ hL_comp hψ_L ν
      -- Pointwise a.e. identity on `L_ball`
      have hae_grad : ∀ᵐ x ∂volume.restrict L_ball,
          ψ x * ‖gradient W_lim x - (W_lim x / (max (inner ℝ ν x) 0 + ε)) • ν‖ ^ 2 =
            ψ x * ‖gradient W_lim x‖ ^ 2 - inner ℝ (gradient uε x) ν * ψ x := by
        filter_upwards [ae_restrict_mem hL_comp.measurableSet,
          ae_restrict_of_ae (ae_differentiableAt_lipschitz hW),
          ae_restrict_of_ae hnull_hyp] with x hxL hdx hne
        have hx_ball : x ∈ ball (0 : Space (m + 1)) (R_B + 3) := by
          have hnx : ‖x‖ ≤ R_B + 2 := by
            simpa only [L_ball, mem_closedBall, dist_zero_right] using hxL
          rw [mem_ball, dist_zero_right]
          linarith
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · -- Negative halfspace: `W_lim` and `uε` vanish on a neighborhood of `x`
          have hopen : IsOpen {y : Space (m + 1) | inner ℝ ν y < 0} :=
            isOpen_lt (continuous_const.inner continuous_id) continuous_const
          have hevW : W_lim =ᶠ[𝓝 x] 0 := by
            filter_upwards [hopen.mem_nhds hlt] with y hy
            exact hW_zero_half y (le_of_lt hy)
          have hevu : uε =ᶠ[𝓝 x] 0 := by
            filter_upwards [hopen.mem_nhds hlt] with y hy
            simp [uε, hW_zero_half y (le_of_lt hy)]
          have hgW : gradient W_lim x = 0 := by
            rw [hevW.gradient_eq]; simp [gradient]
          have hgu : gradient uε x = 0 := by
            rw [hevu.gradient_eq]; simp [gradient]
          rw [hgW, hgu, hW_zero_half x (le_of_lt hlt)]
          simp
        · -- Positive halfspace: `uε y = W_lim y ^ 2 / (inner ℝ ν y + ε)` near `x`
          have hopen : IsOpen (ball (0 : Space (m + 1)) (R_B + 3) ∩
              {y : Space (m + 1) | 0 < inner ℝ ν y}) :=
            isOpen_ball.inter (isOpen_lt continuous_const (continuous_const.inner continuous_id))
          have hevu : uε =ᶠ[𝓝 x] fun y ↦ W_lim y ^ 2 * (inner ℝ ν y + ε)⁻¹ := by
            filter_upwards [hopen.mem_nhds ⟨hx_ball, hgt⟩] with y ⟨hyb, hyp⟩
            have hθ1 : (θ : Space (m + 1) → ℝ) y = 1 :=
              θ.one_of_mem_closedBall (ball_subset_closedBall hyb)
            dsimp only [uε]
            rw [hθ1, one_mul, max_eq_left hyp.le, div_eq_mul_inv]
          have hden_pos : 0 < inner ℝ ν x + ε := add_pos hgt hε
          have hd_num : HasFDerivAt (fun y ↦ W_lim y ^ 2)
              ((2 * W_lim x) • fderiv ℝ W_lim x) x :=
            (hdx.hasFDerivAt.pow 2).congr_fderiv (by
              ext v
              simp only [Nat.add_one_sub_one, pow_one, smul_apply, nsmul_eq_mul,
                Nat.cast_ofNat, smul_eq_mul])
          have hd_den : HasFDerivAt (fun y : Space (m + 1) ↦ inner ℝ ν y + ε)
              (toDual ℝ (Space (m + 1)) ν) x := by
            have hin : HasFDerivAt (fun y : Space (m + 1) ↦ inner ℝ ν y)
                (toDual ℝ (Space (m + 1)) ν) x :=
              ((hasFDerivAt_const ν x).inner ℝ (hasFDerivAt_id x)).congr_fderiv (by
                ext v
                simp [fderivInnerCLM_apply, toDual_apply_apply])
            simpa using hin.add_const ε
          have hd_inv : HasFDerivAt (fun y : Space (m + 1) ↦ (inner ℝ ν y + ε)⁻¹)
              ((-((inner ℝ ν x + ε) ^ 2)⁻¹) • toDual ℝ (Space (m + 1)) ν) x := by
            have hi := (hasDerivAt_inv hden_pos.ne').comp_hasFDerivAt x hd_den
            exact hi.congr_fderiv (by
              ext v
              simp only [smul_apply, toDual_apply_apply, smul_eq_mul])
          have hd_quot := (hd_num.mul hd_inv).congr_of_eventuallyEq hevu
          have hgu_ν : inner ℝ (gradient uε x) ν =
              (2 * (inner ℝ ν x + ε) * W_lim x * inner ℝ (gradient W_lim x) ν -
                W_lim x ^ 2) / (inner ℝ ν x + ε) ^ 2 := by
            rw [inner_gradient_left, hd_quot.fderiv]
            simp only [add_apply, smul_apply, toDual_apply_apply, real_inner_self_eq_norm_sq,
              hν, one_pow, smul_eq_mul, ← inner_gradient_left]
            have hne_d : inner ℝ ν x + ε ≠ 0 := hden_pos.ne'
            field_simp [hne_d]
            ring
          rw [max_eq_left hgt.le, norm_sub_sq_real, norm_smul, hν, mul_one,
            Real.norm_of_nonneg (div_nonneg (hW0 x) hden_pos.le), real_inner_smul_right, hgu_ν]
          have hne_den : inner ℝ ν x + ε ≠ 0 := hden_pos.ne'
          field_simp [hne_den]
          ring
      have hi_gW : IntegrableOn (fun x ↦ ψ x * ‖gradient W_lim x‖ ^ 2) L_ball := by
        apply ((continuousOn_const (s := L_ball) (c := κ ^ 2)).integrableOn_compact hL_comp).mono'
          (hψ.continuous.measurable.mul
            ((measurable_gradient W_lim).norm.pow_const 2)).aestronglyMeasurable
        filter_upwards with x
        dsimp only [Pi.mul_apply]
        rw [norm_mul, Real.norm_of_nonneg χ₁.nonneg, Real.norm_of_nonneg (sq_nonneg _)]
        simpa only [one_mul] using
          mul_le_mul χ₁.le_one (pow_le_pow_left₀ (norm_nonneg _) (hW_grad_le x) 2)
            (sq_nonneg _) zero_le_one
      have hi_gu0 : IntegrableOn (fun x ↦ inner ℝ (gradient uε x) ν) L_ball :=
        (integrableOn_gradient_of_locallyLipschitz huε_lip hL_comp).inner_const ν
      have hi_gu : IntegrableOn (fun x ↦ inner ℝ (gradient uε x) ν * ψ x) L_ball :=
        hi_gu0.mul_continuousOn hψ.continuous.continuousOn hL_comp
      rw [integral_congr_ae hae_grad, integral_sub hi_gW hi_gu, hibp, htrunc_ψ]
      have hfd_eq : (∫ x in L_ball, uε x * fderiv ℝ ψ x ν) =
          ∫ x in L_ball, 2 * deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2) *
            (max (inner ℝ ν x) 0 / (max (inner ℝ ν x) 0 + ε)) * W_lim x ^ 2 := by
        apply setIntegral_congr_fun hL_comp.measurableSet
        intro x hxL
        have hx_ball : x ∈ ball (0 : Space (m + 1)) (R_B + 3) := by
          have hnx : ‖x‖ ≤ R_B + 2 := by
            simpa only [L_ball, mem_closedBall, dist_zero_right] using hxL
          rw [mem_ball, dist_zero_right]; linarith
        have hθ1 : (θ : Space (m + 1) → ℝ) x = 1 :=
          θ.one_of_mem_closedBall (ball_subset_closedBall hx_ball)
        have hfd : fderiv ℝ ψ x ν = 2 * deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2) * inner ℝ ν x := by
          rw [(hasFDerivAt_radialNormSq hχ₁_cd x).fderiv]
          simp [toDual_apply_apply, real_inner_comm]
        dsimp only [uε]
        rw [hθ1, one_mul, hfd]
        by_cases hnp : inner ℝ ν x ≤ 0
        · rw [hW_zero_half x hnp, max_eq_right hnp]
          ring
        · push Not at hnp
          rw [max_eq_left hnp.le]
          ring
      rw [hfd_eq, sub_neg_eq_add]
      have hi_a : IntegrableOn
          (fun x ↦ 2 * deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2) * W_lim x ^ 2) L_ball :=
        ((continuous_const.mul ((hχ₁_cd.continuous_deriv le_rfl).comp
          (continuous_norm.pow 2))).mul (hW.continuous.pow 2)).continuousOn.integrableOn_compact
          hL_comp
      have hi_b : IntegrableOn
          (fun x ↦ 2 * deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2) *
            (max (inner ℝ ν x) 0 / (max (inner ℝ ν x) 0 + ε)) * W_lim x ^ 2) L_ball := by
        have hcd : Continuous (fun x : Space (m + 1) ↦ max (inner ℝ ν x) 0 + ε) :=
          (((continuous_const (y := ν)).inner continuous_id).max
            (continuous_const (y := (0 : ℝ)))).add (continuous_const (y := ε))
        exact (((continuous_const.mul ((hχ₁_cd.continuous_deriv le_rfl).comp
          (continuous_norm.pow 2))).mul
            ((((continuous_const (y := ν)).inner continuous_id).max
              (continuous_const (y := (0 : ℝ)))).div hcd
              (fun x ↦ (add_pos_of_nonneg_of_pos (le_max_right _ _) hε).ne'))).mul
                (hW.continuous.pow 2)).continuousOn.integrableOn_compact hL_comp
      have hadd_ab := integral_add hi_a.neg hi_b
      dsimp only [Pi.add_apply, Pi.neg_apply] at hadd_ab
      rw [← integral_neg, ← hadd_ab, ← integral_neg]
      apply setIntegral_congr_fun hL_comp.measurableSet
      intro x _
      have hden_ne : max (inner ℝ ν x) 0 + ε ≠ 0 :=
        (add_pos_of_nonneg_of_pos (le_max_right _ _) hε).ne'
      field_simp [hden_ne]
      ring
    -- Pass `ε = 1 / (k + 1) → 0` on the slab `K_slab := closedBall 0 R_B ∩ {x | δ ≤ inner ℝ ν x}`
    let K_slab : Set (Space (m + 1)) := closedBall 0 R_B ∩ {x | δ ≤ inner ℝ ν x}
    have hK_slab : IsCompact K_slab :=
      (isCompact_closedBall 0 R_B).inter_right
        (isClosed_le continuous_const (continuous_const.inner continuous_id))
    have hK_sub_L : K_slab ⊆ L_ball :=
      inter_subset_left.trans (closedBall_subset_closedBall (by linarith))
    let ε_seq : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
    have hε_pos (k : ℕ) : 0 < ε_seq k := by dsimp only [ε_seq]; positivity
    have hε_lim : Tendsto ε_seq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ht_rhs : Tendsto (fun k ↦ -∫ x in L_ball, 2 * deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2) *
        (ε_seq k / (max (inner ℝ ν x) 0 + ε_seq k)) * W_lim x ^ 2) atTop (𝓝 0) := by
      suffices h0 : Tendsto (fun k ↦ ∫ x in L_ball, 2 * deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2) *
          (ε_seq k / (max (inner ℝ ν x) 0 + ε_seq k)) * W_lim x ^ 2) atTop
          (𝓝 (∫ _x in L_ball, (0 : ℝ))) by
        simpa only [integral_zero, neg_zero] using h0.neg
      obtain ⟨Cd, hCd⟩ := hL_comp.exists_bound_of_continuousOn
        ((hχ₁_cd.continuous_deriv le_rfl).comp (continuous_norm.pow 2)).continuousOn
      apply tendsto_integral_of_dominated_convergence
        (fun _ ↦ 2 * |Cd| * (κ * (R_B + 2)) ^ 2)
      · intro k
        have hcd : Continuous (fun x : Space (m + 1) ↦ max (inner ℝ ν x) 0 + ε_seq k) :=
          (((continuous_const (y := ν)).inner continuous_id).max
            (continuous_const (y := (0 : ℝ)))).add (continuous_const (y := ε_seq k))
        exact (((continuous_const.mul ((hχ₁_cd.continuous_deriv le_rfl).comp
          (continuous_norm.pow 2))).mul ((continuous_const (y := ε_seq k)).div hcd
            (fun x ↦ (add_pos_of_nonneg_of_pos (le_max_right _ _) (hε_pos k)).ne'))).mul
              (hW.continuous.pow 2)).aestronglyMeasurable
      · exact continuousOn_const.integrableOn_compact hL_comp
      · intro k
        filter_upwards [ae_restrict_mem hL_comp.measurableSet] with x hxL
        have hnx : ‖x‖ ≤ R_B + 2 := by
          simpa only [L_ball, mem_closedBall, dist_zero_right] using hxL
        have hWx : W_lim x ≤ κ * (R_B + 2) := by
          have hd := hW.dist_le_mul x 0
          rw [hW_zero, Real.dist_eq, sub_zero, dist_zero_right] at hd
          exact (le_abs_self _).trans (hd.trans (mul_le_mul_of_nonneg_left hnx hκ.le))
        have hrat : |ε_seq k / (max (inner ℝ ν x) 0 + ε_seq k)| ≤ 1 := by
          rw [abs_of_pos (div_pos (hε_pos k)
            (add_pos_of_nonneg_of_pos (le_max_right _ _) (hε_pos k))),
            div_le_one (add_pos_of_nonneg_of_pos (le_max_right _ _) (hε_pos k))]
          exact le_add_of_nonneg_left (le_max_right _ _)
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (sq_nonneg (W_lim x))]
        have hd_le : |deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2)| ≤ |Cd| :=
          (hCd x hxL).trans (le_abs_self Cd)
        calc
          2 * |deriv (χ₁ : ℝ → ℝ) (‖x‖ ^ 2)| *
              |ε_seq k / (max (inner ℝ ν x) 0 + ε_seq k)| * W_lim x ^ 2 ≤
            2 * |Cd| * 1 * (κ * (R_B + 2)) ^ 2 := by
            apply mul_le_mul
            · exact mul_le_mul (mul_le_mul_of_nonneg_left hd_le (by norm_num)) hrat
                (abs_nonneg _) (by positivity)
            · exact pow_le_pow_left₀ (hW0 x) hWx 2
            · exact sq_nonneg _
            · positivity
          _ = 2 * |Cd| * (κ * (R_B + 2)) ^ 2 := by ring
      · filter_upwards with x
        by_cases hnp : inner ℝ ν x ≤ 0
        · simp [hW_zero_half x hnp]
        · push Not at hnp
          have hden_lim : Tendsto (fun k ↦ max (inner ℝ ν x) 0 + ε_seq k)
              atTop (𝓝 (inner ℝ ν x)) := by
            rw [max_eq_left hnp.le]
            simpa only [add_zero] using tendsto_const_nhds.add hε_lim
          have hq : Tendsto (fun k ↦ ε_seq k / (max (inner ℝ ν x) 0 + ε_seq k))
              atTop (𝓝 (0 / inner ℝ ν x)) := hε_lim.div hden_lim hnp.ne'
          simp only [zero_div] at hq
          simpa using (tendsto_const_nhds.mul hq).mul tendsto_const_nhds
    have ht_slab : Tendsto (fun k ↦ ∫ x in K_slab,
        ‖gradient W_lim x - (W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ ^ 2)
        atTop (𝓝 0) := by
      apply squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) _
        (ht_rhs.congr' (Eventually.of_forall (fun k ↦ (hpicone_eps (ε_seq k) (hε_pos k)).symm)))
      intro k
      have hiL : IntegrableOn (fun x ↦ ψ x *
          ‖gradient W_lim x - (W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ ^ 2) L_ball := by
        have hcd : Continuous (fun x : Space (m + 1) ↦ max (inner ℝ ν x) 0 + ε_seq k) :=
          (((continuous_const (y := ν)).inner continuous_id).max
            (continuous_const (y := (0 : ℝ)))).add (continuous_const (y := ε_seq k))
        apply (continuousOn_const.integrableOn_compact hL_comp (f := fun _ ↦ (2 * κ) ^ 2)).mono'
          (hψ.continuous.measurable.mul (((measurable_gradient W_lim).sub
            ((hW.continuous.div hcd (fun x ↦ (add_pos_of_nonneg_of_pos (le_max_right _ _)
              (hε_pos k)).ne')).measurable.smul_const ν)).norm.pow_const 2)).aestronglyMeasurable
        filter_upwards with x
        have hq_le : W_lim x / (max (inner ℝ ν x) 0 + ε_seq k) ≤ κ := by
          rw [div_le_iff₀ (add_pos_of_nonneg_of_pos (le_max_right _ _) (hε_pos k))]
          exact (hW_le x).trans (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (hε_pos k).le) hκ.le)
        have hn_le : ‖gradient W_lim x -
            (W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ ≤ 2 * κ := by
          calc
            ‖gradient W_lim x - (W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ ≤
                ‖gradient W_lim x‖ + ‖(W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ :=
              norm_sub_le _ _
            _ ≤ κ + κ := by
              rw [norm_smul, hν, mul_one, Real.norm_of_nonneg (div_nonneg (hW0 x)
                (add_pos_of_nonneg_of_pos (le_max_right _ _) (hε_pos k)).le)]
              exact add_le_add (hW_grad_le x) hq_le
            _ = 2 * κ := by ring
        dsimp only [Pi.mul_apply, Pi.sub_apply]
        rw [norm_mul, Real.norm_of_nonneg χ₁.nonneg, Real.norm_of_nonneg (sq_nonneg _)]
        exact (mul_le_of_le_one_left (sq_nonneg _) χ₁.le_one).trans
          (pow_le_pow_left₀ (norm_nonneg _) hn_le 2)
      have heq_on : (∫ x in K_slab,
          ‖gradient W_lim x - (W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ ^ 2) =
          ∫ x in K_slab, ψ x *
            ‖gradient W_lim x - (W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ ^ 2 := by
        apply setIntegral_congr_fun hK_slab.measurableSet
        intro x hx
        dsimp only
        rw [hψ_one x hx.1, one_mul]
      rw [heq_on]
      exact setIntegral_mono_set hiL
        (Eventually.of_forall (fun _ ↦ mul_nonneg χ₁.nonneg (sq_nonneg _)))
        (Eventually.of_forall hK_sub_L)
    have ht_lim : Tendsto (fun k ↦ ∫ x in K_slab,
        ‖gradient W_lim x - (W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ ^ 2)
        atTop (𝓝 (∫ x in K_slab, ‖gradient W_lim x - (W_lim x / inner ℝ ν x) • ν‖ ^ 2)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ ↦ (2 * κ) ^ 2)
      · intro k
        have hcd : Continuous (fun x : Space (m + 1) ↦ max (inner ℝ ν x) 0 + ε_seq k) :=
          (((continuous_const (y := ν)).inner continuous_id).max
            (continuous_const (y := (0 : ℝ)))).add (continuous_const (y := ε_seq k))
        exact (((measurable_gradient W_lim).sub
          ((hW.continuous.div hcd (fun x ↦ (add_pos_of_nonneg_of_pos (le_max_right _ _)
            (hε_pos k)).ne')).measurable.smul_const ν)).norm.pow_const 2).aestronglyMeasurable
      · exact continuousOn_const.integrableOn_compact hK_slab
      · intro k
        filter_upwards with x
        have hq_le : W_lim x / (max (inner ℝ ν x) 0 + ε_seq k) ≤ κ := by
          rw [div_le_iff₀ (add_pos_of_nonneg_of_pos (le_max_right _ _) (hε_pos k))]
          exact (hW_le x).trans (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (hε_pos k).le) hκ.le)
        have hn_le : ‖gradient W_lim x -
            (W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ ≤ 2 * κ := by
          calc
            ‖gradient W_lim x - (W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ ≤
                ‖gradient W_lim x‖ + ‖(W_lim x / (max (inner ℝ ν x) 0 + ε_seq k)) • ν‖ :=
              norm_sub_le _ _
            _ ≤ κ + κ := by
              rw [norm_smul, hν, mul_one, Real.norm_of_nonneg (div_nonneg (hW0 x)
                (add_pos_of_nonneg_of_pos (le_max_right _ _) (hε_pos k)).le)]
              exact add_le_add (hW_grad_le x) hq_le
            _ = 2 * κ := by ring
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hn_le 2
      · filter_upwards [ae_restrict_mem hK_slab.measurableSet] with x hx
        have hpos : 0 < inner ℝ ν x := hδ.trans_le hx.2
        have hden : Tendsto (fun k ↦ max (inner ℝ ν x) 0 + ε_seq k)
            atTop (𝓝 (inner ℝ ν x)) := by
          rw [max_eq_left hpos.le]
          simpa only [add_zero] using tendsto_const_nhds.add hε_lim
        exact ((tendsto_const_nhds.sub
          ((tendsto_const_nhds.div hden hpos.ne').smul_const ν)).norm.pow 2)
    exact tendsto_nhds_unique ht_lim ht_slab
  -- Step 2: Exhaust `{x | 0 < inner ℝ ν x}` by countable slabs to conclude tangential derivatives
  -- vanish almost everywhere on all of `Space (m + 1)`.
  have hae_pos : ∀ᵐ x, 0 < inner ℝ ν x →
      gradient W_lim x = (W_lim x / inner ℝ ν x) • ν := by
    have hk (k : ℕ) : ∀ᵐ x,
        x ∈ closedBall 0 ((k : ℝ) + 1) ∩ {x | 1 / ((k : ℝ) + 1) ≤ inner ℝ ν x} →
          gradient W_lim x = (W_lim x / inner ℝ ν x) • ν := by
      let S_k : Set (Space (m + 1)) :=
        closedBall 0 ((k : ℝ) + 1) ∩ {x | 1 / ((k : ℝ) + 1) ≤ inner ℝ ν x}
      have hSk : IsCompact S_k :=
        (isCompact_closedBall 0 ((k : ℝ) + 1)).inter_right
          (isClosed_le continuous_const (continuous_const.inner continuous_id))
      have hiSk : IntegrableOn
          (fun x ↦ ‖gradient W_lim x - (W_lim x / inner ℝ ν x) • ν‖ ^ 2) S_k := by
        apply (continuousOn_const.integrableOn_compact hSk (f := fun _ ↦ (2 * κ) ^ 2)).mono'
          (((measurable_gradient W_lim).sub
            ((hW.continuous.measurable.div (continuous_const.inner continuous_id).measurable)
              |>.smul_const ν)).norm.pow_const 2).aestronglyMeasurable
        filter_upwards [ae_restrict_mem hSk.measurableSet] with x hx
        have hpos : 0 < inner ℝ ν x := (by positivity : 0 < 1 / ((k : ℝ) + 1)).trans_le hx.2
        have hq_le : W_lim x / inner ℝ ν x ≤ κ := by
          rw [div_le_iff₀ hpos]
          simpa only [max_eq_left hpos.le] using hW_le x
        have hn_le : ‖gradient W_lim x - (W_lim x / inner ℝ ν x) • ν‖ ≤ 2 * κ := by
          calc
            ‖gradient W_lim x - (W_lim x / inner ℝ ν x) • ν‖ ≤
                ‖gradient W_lim x‖ + ‖(W_lim x / inner ℝ ν x) • ν‖ := norm_sub_le _ _
            _ ≤ κ + κ := by
              rw [norm_smul, hν, mul_one, Real.norm_of_nonneg (div_nonneg (hW0 x) hpos.le)]
              exact add_le_add (hW_grad_le x) hq_le
            _ = 2 * κ := by ring
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hn_le 2
      have hae0 := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall (fun _ ↦ sq_nonneg _)) hiSk).mp
        (hslab_zero ((k : ℝ) + 1) (1 / ((k : ℝ) + 1)) (by positivity) (by positivity))
      rw [EventuallyEq, ae_restrict_iff' hSk.measurableSet] at hae0
      filter_upwards [hae0] with x hx hmem
      have h0 : ‖gradient W_lim x - (W_lim x / inner ℝ ν x) • ν‖ = 0 :=
        sq_eq_zero_iff.mp (hx hmem)
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
    filter_upwards [ae_all_iff.mpr hk] with x hx hpos
    obtain ⟨k₁, hk₁⟩ := exists_nat_gt ‖x‖
    obtain ⟨k₂, hk₂⟩ := exists_nat_gt (1 / inner ℝ ν x)
    let k := max k₁ k₂
    apply hx k
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have h1 : (k₁ : ℝ) ≤ k := Nat.cast_le.mpr (le_max_left _ _)
      linarith
    · change 1 / ((k : ℝ) + 1) ≤ inner ℝ ν x
      have h2 : (k₂ : ℝ) ≤ k := Nat.cast_le.mpr (le_max_right _ _)
      have hgt : 1 / inner ℝ ν x < (k : ℝ) + 1 := by linarith
      rw [div_le_iff₀ (by positivity)]
      have hlt' := (div_lt_iff₀ hpos).mp hgt
      linarith
  have htang : ∀ ξ : Space (m + 1), inner ℝ ν ξ = 0 → ∀ᵐ x, fderiv ℝ W_lim x ξ = 0 := by
    intro ξ hξ
    filter_upwards [hae_pos, hnull_hyp] with x hpos hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hopen : IsOpen {y : Space (m + 1) | inner ℝ ν y < 0} :=
        isOpen_lt (continuous_const.inner continuous_id) continuous_const
      have hev : W_lim =ᶠ[𝓝 x] 0 := by
        filter_upwards [hopen.mem_nhds hlt] with y hy
        exact hW_zero_half y (le_of_lt hy)
      rw [hev.fderiv_eq]
      simp
    · rw [← inner_gradient_left, hpos hgt, real_inner_smul_left, hξ, mul_zero]
  have hprof := eq_normal_profile_of_ae_tangential_fderiv_eq_zero hW hν htang
  let c := W_lim ν
  have hform (x : Space (m + 1)) : W_lim x = c * max (inner ℝ ν x) 0 := by
    by_cases hx : inner ℝ ν x ≤ 0
    · rw [hW_zero_half x hx, max_eq_right hx, mul_zero]
    · push Not at hx
      rw [hprof x, hW_homog (inner ℝ ν x) hx.le ν, max_eq_left hx.le, mul_comm]
  have hc_le : c ≤ κ := by
    have hle := hW_le ν
    simpa only [c, real_inner_self_eq_norm_sq, hν, one_pow, max_eq_left zero_le_one, mul_one]
      using hle
  have hc_pos : 0 < c := by
    obtain ⟨x₀, _, hx₀⟩ := hnondeg
    rw [hform x₀] at hx₀
    exact pos_of_mul_pos_left hx₀ (le_max_right _ _)
  exact ⟨c, ⟨hc_pos, hc_le⟩, hform⟩

/-! ### TB6: Rescaled stress stationarity identifies `c = κ` and full-family normal slope -/

/-- Gradient of `x ↦ c * max (inner ℝ ν x) 0` away from the orthogonal hyperplane. -/
private theorem gradient_halfspace_linear_pos {d : ℕ} {ν x : Space d} (c : ℝ)
    (hx : inner ℝ ν x ≠ 0) :
    gradient (fun y ↦ c * max (inner ℝ ν y) 0) x =
      {y : Space d | 0 < inner ℝ ν y}.indicator (fun _ ↦ c • ν) x := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hopen : IsOpen {y : Space d | inner ℝ ν y < 0} :=
      isOpen_lt (continuous_const.inner continuous_id) continuous_const
    have hev : (fun y ↦ c * max (inner ℝ ν y) 0) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hopen.mem_nhds hlt] with y hy
      simp [max_eq_right (le_of_lt hy)]
    have hnmem : x ∉ {y : Space d | 0 < inner ℝ ν y} := not_lt.mpr (le_of_lt hlt)
    rw [hev.gradient_eq, indicator_of_notMem hnmem]
    simp [gradient]
  · have hopen : IsOpen {y : Space d | 0 < inner ℝ ν y} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_id)
    have hev : (fun y ↦ c * max (inner ℝ ν y) 0) =ᶠ[𝓝 x] fun y ↦ c * inner ℝ ν y := by
      filter_upwards [hopen.mem_nhds hgt] with y hy
      simp [max_eq_left (le_of_lt hy)]
    have hin : HasFDerivAt (fun y : Space d ↦ c * inner ℝ ν y)
        (toDual ℝ (Space d) (c • ν)) x := by
      have h0 : HasFDerivAt (fun y : Space d ↦ inner ℝ ν y) (toDual ℝ (Space d) ν) x :=
        ((hasFDerivAt_const ν x).inner ℝ (hasFDerivAt_id x)).congr_fderiv (by
          ext v; simp [fderivInnerCLM_apply, toDual_apply_apply])
      exact (h0.const_mul c).congr_fderiv (by
        ext v; simp [toDual_apply_apply])
    have hmem : x ∈ {y : Space d | 0 < inner ℝ ν y} := hgt
    rw [indicator_of_mem hmem]
    apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left, (hin.congr_of_eventuallyEq hev).fderiv, toDual_apply_apply]

/-- Divergence of a constant-direction vector field `x ↦ φ x • ν`. -/
private theorem fieldDivergence_smul_const {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ) (ν x : Space d) :
    fieldDivergence b (fun y ↦ φ y • ν) x = fderiv ℝ φ x ν := by
  have hd : HasFDerivAt (fun y ↦ φ y • ν) ((fderiv ℝ φ x).smulRight ν) x :=
    (hφ.differentiable one_ne_zero x).hasFDerivAt.smul_const ν
  unfold fieldDivergence
  simp_rw [hd.fderiv, ContinuousLinearMap.smulRight_apply, real_inner_smul_right, ← mul_comm (inner ℝ (b _) ν)]
  have hsum : (∑ i, inner ℝ (b i) ν * fderiv ℝ φ x (b i)) =
      fderiv ℝ φ x (∑ i, inner ℝ (b i) ν • b i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ by rw [map_smul, smul_eq_mul])
  rw [hsum, b.sum_repr' ν]

/-- **Slope identification via stress stationarity (TB6.1–TB6.2)**:
If a physical translation limit `V` with `V 0 = 0` and exterior zero ball `ball (-(R • ν)) R`
has a microscopic blowup `W_lim x = c * max (inner ℝ ν x) 0` (`c > 0`) along `r_seq → 0⁺` with
strong `L²_loc` gradient convergence, then `c = κ`. -/
theorem RigidityHypotheses.halfspace_linear_pos_slope_eq_kappa
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ c R : ℝ}
    {ν : Space (m + 1)} {p_seq : ℕ → Space (m + 1)} {r_seq : ℕ → ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hν : ‖ν‖ = 1) (hR : 0 < R) (hc_pos : 0 < c) (hc_le : c ≤ κ)
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1) (hV0 : V 0 = 0)
    (hzero_ball : ball (-(R • ν)) R ⊆ {x | V x = 0})
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V atTop K)
    (hr_pos : ∀ j, 0 < r_seq j) (hr_lim : Tendsto r_seq atTop (𝓝 0))
    (hWlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ V (r_seq j • x) / r_seq j)
        (fun x ↦ c * max (inner ℝ ν x) 0) atTop K)
    (hgrad : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K,
        ‖gradient (fun y ↦ V (r_seq j • y) / r_seq j) x -
          gradient (fun y ↦ c * max (inner ℝ ν y) 0) x‖ ^ 2) atTop (𝓝 0)) :
    c = κ := by
  have hκ : 0 < κ := h.kappa_pos
  let b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  let W_lim : Space (m + 1) → ℝ := fun x ↦ c * max (inner ℝ ν x) 0
  have hW_lip : LipschitzWith ⟨κ, h.kappa_pos.le⟩ W_lim := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |W_lim x - W_lim y| ≤ κ * dist x y
    dsimp only [W_lim]
    rw [← mul_sub, abs_mul, abs_of_pos hc_pos]
    have hm : |max (inner ℝ ν x) 0 - max (inner ℝ ν y) 0| ≤ ‖x - y‖ :=
      (abs_max_sub_max_le_abs _ _ 0).trans (by
        rw [← inner_sub_right]
        exact (abs_real_inner_le_norm ν (x - y)).trans (by rw [hν, one_mul]))
    rw [dist_eq_norm]
    exact (mul_le_mul_of_nonneg_left hm hc_pos.le).trans
      (mul_le_mul_of_nonneg_right hc_le (norm_nonneg _))
  let φ : ContDiffBump (0 : Space (m + 1)) :=
    { rIn := 1, rOut := 2, rIn_pos := zero_lt_one, rIn_lt_rOut := one_lt_two }
  let K : Set (Space (m + 1)) := closedBall 0 2
  have hK : IsCompact K := isCompact_closedBall 0 2
  have hφ_cd : ContDiff ℝ 1 (φ : Space (m + 1) → ℝ) := φ.contDiff
  have hcφ : HasCompactSupport (φ : Space (m + 1) → ℝ) := φ.hasCompactSupport
  have hφ_supp : tsupport (φ : Space (m + 1) → ℝ) ⊆ K := by
    rw [φ.tsupport_eq]
  let X : Space (m + 1) → Space (m + 1) := fun x ↦ (φ : Space (m + 1) → ℝ) x • ν
  have hX : ContDiff ℝ 1 X := hφ_cd.smul contDiff_const
  have hcX : HasCompactSupport X := hcφ.smul_right
  have hX_supp : tsupport X ⊆ K :=
    (tsupport_smul_subset_left (φ : Space (m + 1) → ℝ) (fun _ ↦ ν)).trans hφ_supp
  -- Rescaled stress stationarity at scale `r_seq j`
  let v : ℕ → Space (m + 1) → ℝ := fun j x ↦ V (r_seq j • x) / r_seq j
  have hv_lip (j : ℕ) : LipschitzWith ⟨κ, h.kappa_pos.le⟩ (v j) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |v j x - v j y| ≤ κ * dist x y
    dsimp only [v]
    rw [← sub_div, abs_div, abs_of_pos (hr_pos j), div_le_iff₀ (hr_pos j)]
    have hd := hV.dist_le_mul (r_seq j • x) (r_seq j • y)
    rw [Real.dist_eq, dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (hr_pos j).le, ← dist_eq_norm] at hd
    change |V (r_seq j • x) - V (r_seq j • y)| ≤ κ * (r_seq j * dist x y) at hd
    nlinarith
  have hstress_j (j : ℕ) :
      (∫ x in K, ((‖gradient (v j) x‖ ^ 2 / 2 +
          {y : Space (m + 1) | 0 < V (r_seq j • y)}.indicator
            (fun y ↦ normalizedPotential f (V (r_seq j • y))) x) *
          fderiv ℝ (φ : Space (m + 1) → ℝ) x ν -
        inner ℝ (gradient (v j) x)
          ((fderiv ℝ (φ : Space (m + 1) → ℝ) x (gradient (v j) x)) • ν))) = 0 := by
    let rj := r_seq j
    have hrj : 0 < rj := hr_pos j
    have hrj_ne : rj ≠ 0 := hrj.ne'
    let Xj : Space (m + 1) → Space (m + 1) := fun y ↦ X (rj⁻¹ • y)
    have hXj : ContDiff ℝ 1 Xj :=
      hX.comp ((contDiff_const (c := rj⁻¹)).smul contDiff_id)
    have hcXj : HasCompactSupport Xj :=
      hcX.comp_homeomorph (Homeomorph.smul (Units.mk0 rj⁻¹ (inv_ne_zero hrj_ne)))
    have h0 := hr.physical_translation_limit_stress_stationarity h hV hval hlim b hXj hcXj
    -- Rescale `y = rj • x` via `Measure.integral_comp_smul`
    let F_y : Space (m + 1) → ℝ := fun y ↦
      phaseEnergyDensity f 0 V y * fieldDivergence b Xj y -
        inner ℝ (gradient V y) (fderiv ℝ Xj y (gradient V y))
    have hint0 : (∫ x, F_y (rj • x)) = 0 := by
      have hchg := Measure.integral_comp_smul volume F_y rj
      simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchg
      rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hrj.le (m + 1))), h0, mul_zero] at hchg
      exact hchg
    have hpoint (x : Space (m + 1)) :
        F_y (rj • x) = rj⁻¹ * (((‖gradient (v j) x‖ ^ 2 / 2 +
            {y : Space (m + 1) | 0 < V (rj • y)}.indicator
              (fun y ↦ normalizedPotential f (V (rj • y))) x) *
            fderiv ℝ (φ : Space (m + 1) → ℝ) x ν -
          inner ℝ (gradient (v j) x)
            ((fderiv ℝ (φ : Space (m + 1) → ℝ) x (gradient (v j) x)) • ν))) := by
      have hlin : HasFDerivAt (fun y : Space (m + 1) ↦ rj⁻¹ • y)
          (rj⁻¹ • ContinuousLinearMap.id ℝ (Space (m + 1))) (rj • x) :=
        (rj⁻¹ • ContinuousLinearMap.id ℝ (Space (m + 1))).hasFDerivAt
      have hdX : HasFDerivAt X (fderiv ℝ X x) (rj⁻¹ • (rj • x)) := by
        rw [inv_smul_smul₀ hrj_ne]
        exact (hX.differentiable one_ne_zero x).hasFDerivAt
      have hfXj : fderiv ℝ Xj (rj • x) = rj⁻¹ • fderiv ℝ X x := by
        change fderiv ℝ (X ∘ fun y : Space (m + 1) ↦ rj⁻¹ • y) (rj • x) = _
        rw [(hdX.comp (rj • x) hlin).fderiv]
        ext w
        simp
      have hdivXj : fieldDivergence b Xj (rj • x) =
          rj⁻¹ * fderiv ℝ (φ : Space (m + 1) → ℝ) x ν := by
        unfold fieldDivergence
        simp_rw [hfXj]
        simp only [smul_apply, real_inner_smul_right, ← Finset.mul_sum]
        congr 1
        exact fieldDivergence_smul_const b hφ_cd ν x
      have hfX_apply (w : Space (m + 1)) :
          fderiv ℝ X x w = (fderiv ℝ (φ : Space (m + 1) → ℝ) x w) • ν := by
        have hd : HasFDerivAt X ((fderiv ℝ (φ : Space (m + 1) → ℝ) x).smulRight ν) x :=
          (hφ_cd.differentiable one_ne_zero x).hasFDerivAt.smul_const ν
        rw [hd.fderiv]
        rfl
      have hgV : gradient V (rj • x) = gradient (v j) x :=
        (gradient_rescale_div V hrj_ne x).symm
      dsimp only [F_y, phaseEnergyDensity]
      rw [hdivXj, hfXj, hgV, smul_apply, hfX_apply, real_inner_smul_right]
      by_cases hp : 0 < V (rj • x)
      · have hmem1 : rj • x ∈ {y : Space (m + 1) | 0 < V y} := hp
        have hmem2 : x ∈ {y : Space (m + 1) | 0 < V (rj • y)} := hp
        rw [indicator_of_mem hmem1, indicator_of_mem hmem2, hgV, add_zero]
        ring
      · have hnmem1 : rj • x ∉ {y : Space (m + 1) | 0 < V y} := hp
        have hnmem2 : x ∉ {y : Space (m + 1) | 0 < V (rj • y)} := hp
        have hvj0 : v j x = 0 := by
          dsimp only [v]
          have hV0x : V (rj • x) = 0 := le_antisymm (not_lt.mp hp) (hval (rj • x)).1
          rw [hV0x, zero_div]
        have hgv0 : gradient (v j) x = 0 := by
          by_cases hdv : DifferentiableAt ℝ (v j) x
          · have hmin_v : IsLocalMin (v j) x := by
              filter_upwards with y
              rw [hvj0]
              exact div_nonneg (hval (rj • y)).1 hrj.le
            simp [gradient, hmin_v.fderiv_eq_zero]
          · simp [gradient, fderiv_zero_of_not_differentiableAt hdv]
        rw [indicator_of_notMem hnmem1, indicator_of_notMem hnmem2, hgv0]
        simp
    simp_rw [hpoint, integral_const_mul] at hint0
    have hint_all : (∫ x, ((‖gradient (v j) x‖ ^ 2 / 2 +
          {y : Space (m + 1) | 0 < V (rj • y)}.indicator
            (fun y ↦ normalizedPotential f (V (rj • y))) x) *
          fderiv ℝ (φ : Space (m + 1) → ℝ) x ν -
        inner ℝ (gradient (v j) x)
          ((fderiv ℝ (φ : Space (m + 1) → ℝ) x (gradient (v j) x)) • ν))) = 0 :=
      (mul_eq_zero.mp hint0).resolve_left (inv_ne_zero hrj_ne)
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      have hn : x ∉ tsupport (φ : Space (m + 1) → ℝ) := fun hh ↦ hx (hφ_supp hh)
      simp [fderiv_of_notMem_tsupport ℝ hn])]
    exact hint_all
  -- Pass each of the three integrals on `K` to its limit as `j → ∞`
  obtain ⟨Cf, hCf⟩ := hK.exists_bound_of_continuousOn (hφ_cd.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨Cw, hCw⟩ := isCompact_Icc.exists_bound_of_continuousOn h.normalizedPotential_continuousOn
  have hnull_hyp : ∀ᵐ x, inner ℝ ν x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using measure_orthogonal_hyperplane_eq_zero hν
  -- 1. Potential indicator integral converges to `normalizedPotential f 0 * ∫_{⟨ν,x⟩>0} ∂_ν φ`
  have ht_pot : Tendsto (fun j ↦ ∫ x in K,
      {y : Space (m + 1) | 0 < V (r_seq j • y)}.indicator
        (fun y ↦ normalizedPotential f (V (r_seq j • y))) x *
        fderiv ℝ (φ : Space (m + 1) → ℝ) x ν) atTop
      (𝓝 (∫ x in K, {y : Space (m + 1) | 0 < inner ℝ ν y}.indicator
        (fun _ ↦ normalizedPotential f 0) x *
        fderiv ℝ (φ : Space (m + 1) → ℝ) x ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ |Cw| * |Cf|)
    · intro j
      have hV_sc : Continuous (fun y : Space (m + 1) ↦ V (r_seq j • y)) :=
        hV.continuous.comp ((continuous_const (y := r_seq j)).smul continuous_id)
      have hmeas_set : MeasurableSet {y : Space (m + 1) | 0 < V (r_seq j • y)} :=
        (isOpen_lt (continuous_const (y := (0 : ℝ))) hV_sc).measurableSet
      have hc_comp : Continuous (fun y : Space (m + 1) ↦ normalizedPotential f (V (r_seq j • y))) :=
        h.normalizedPotential_continuousOn.comp_continuous hV_sc (fun y ↦ hval (r_seq j • y))
      exact ((hc_comp.measurable.indicator hmeas_set).mul
        ((hφ_cd.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable
        ).aestronglyMeasurable
    · exact continuousOn_const.integrableOn_compact hK
    · intro j
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK
      have hfd_le : ‖fderiv ℝ (φ : Space (m + 1) → ℝ) x ν‖ ≤ |Cf| := by
        calc
          ‖fderiv ℝ (φ : Space (m + 1) → ℝ) x ν‖ ≤ ‖fderiv ℝ (φ : Space (m + 1) → ℝ) x‖ * ‖ν‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ |Cf| * 1 := mul_le_mul ((hCf x hxK).trans (le_abs_self Cf)) hν.le
            (norm_nonneg _) (abs_nonneg _)
          _ = |Cf| := mul_one _
      rw [norm_mul]
      apply mul_le_mul _ hfd_le (norm_nonneg _) (abs_nonneg _)
      by_cases hp : 0 < V (r_seq j • x)
      · have hmem : x ∈ {y : Space (m + 1) | 0 < V (r_seq j • y)} := hp
        rw [indicator_of_mem hmem]
        exact (hCw _ (hval _)).trans (le_abs_self Cw)
      · have hnmem : x ∉ {y : Space (m + 1) | 0 < V (r_seq j • y)} := hp
        rw [indicator_of_notMem hnmem, norm_zero]
        exact abs_nonneg Cw
    · filter_upwards [ae_restrict_of_ae hnull_hyp] with x hne
      apply Tendsto.mul _ tendsto_const_nhds
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hnmem : x ∉ {y : Space (m + 1) | 0 < inner ℝ ν y} := not_lt.mpr (le_of_lt hlt)
        rw [indicator_of_notMem hnmem]
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_smul_mem_exterior_ball hν hR hr_pos hr_lim hlt] with j hj
        have hV0j : V (r_seq j • x) = 0 := hzero_ball hj
        have hnmemj : x ∉ {y : Space (m + 1) | 0 < V (r_seq j • y)} := by
          simp [hV0j]
        exact (indicator_of_notMem hnmemj _).symm
      · have hmem : x ∈ {y : Space (m + 1) | 0 < inner ℝ ν y} := hgt
        rw [indicator_of_mem hmem]
        have hv_pt : Tendsto (fun j ↦ V (r_seq j • x) / r_seq j) atTop
            (𝓝 (c * inner ℝ ν x)) := by
          have ht := (hWlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
          simpa only [max_eq_left hgt.le] using ht
        have hev_pos : ∀ᶠ j in atTop, 0 < V (r_seq j • x) := by
          filter_upwards [hv_pt.eventually (Ioi_mem_nhds (mul_pos hc_pos hgt))] with j hj
          exact (div_pos_iff_of_pos_right (hr_pos j)).mp hj
        have hV_lim : Tendsto (fun j ↦ V (r_seq j • x)) atTop (𝓝 0) := by
          have hsm : Tendsto (fun j ↦ r_seq j • x) atTop (𝓝 ((0 : ℝ) • x)) :=
            hr_lim.smul_const x
          rw [zero_smul] at hsm
          have hc0 : Tendsto (fun j ↦ V (r_seq j • x)) atTop (𝓝 (V 0)) :=
            (hV.continuous.tendsto 0).comp hsm
          rwa [hV0] at hc0
        have hW_cont0 : Tendsto (fun j ↦ normalizedPotential f (V (r_seq j • x))) atTop
            (𝓝 (normalizedPotential f 0)) :=
          (h.normalizedPotential_continuousOn.continuousWithinAt
            (by norm_num : (0 : ℝ) ∈ Icc 0 1)).tendsto.comp
            (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hV_lim
              (Eventually.of_forall (fun j ↦ hval _)))
        apply hW_cont0.congr'
        filter_upwards [hev_pos] with j hj
        have hmemj : x ∈ {y : Space (m + 1) | 0 < V (r_seq j • y)} := hj
        exact (indicator_of_mem hmemj
          (fun y ↦ normalizedPotential f (V (r_seq j • y)))).symm
  -- 2. Kinetic stress difference converges via strong `L²(K)` gradient convergence `hgrad K hK`
  let Q_stress : (Space (m + 1) → Space (m + 1)) → Space (m + 1) → ℝ :=
    fun q x ↦ (‖q x‖ ^ 2 / 2) * fderiv ℝ (φ : Space (m + 1) → ℝ) x ν -
      inner ℝ (q x) ((fderiv ℝ (φ : Space (m + 1) → ℝ) x (q x)) • ν)
  have ht_kin : Tendsto (fun j ↦ ∫ x in K, Q_stress (gradient (v j)) x) atTop
      (𝓝 (∫ x in K, Q_stress (gradient W_lim) x)) := by
    have hdiff_le : ∀ j, ‖(∫ x in K, Q_stress (gradient (v j)) x) -
        (∫ x in K, Q_stress (gradient W_lim) x)‖ ≤
        (3 * κ * |Cf|) * Real.sqrt ((∫ x in K,
          ‖gradient (v j) x - gradient W_lim x‖ ^ 2) * volume.real K) := by
      intro j
      have hv_gb (x : Space (m + 1)) : ‖gradient (v j) x‖ ≤ κ := by
        rw [gradient, LinearIsometryEquiv.norm_map]
        exact norm_fderiv_le_of_lipschitz ℝ (hv_lip j)
      have hW_gb (x : Space (m + 1)) : ‖gradient W_lim x‖ ≤ κ := by
        rw [gradient, LinearIsometryEquiv.norm_map]
        exact norm_fderiv_le_of_lipschitz ℝ hW_lip
      have hiQ (q : Space (m + 1) → Space (m + 1)) (hqm : Measurable q)
          (hqb : ∀ x, ‖q x‖ ≤ κ) : IntegrableOn (Q_stress q) K := by
        have hmeas_Q : Measurable (Q_stress q) := by
          have hm1 : Measurable (fun x ↦ (‖q x‖ ^ 2 / 2) * fderiv ℝ (φ : Space (m + 1) → ℝ) x ν) :=
            ((hqm.norm.pow_const 2).div_const 2).mul
              ((hφ_cd.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable
          have hm2 : Measurable
              (fun x ↦ inner ℝ (q x) ((fderiv ℝ (φ : Space (m + 1) → ℝ) x (q x)) • ν)) := by
            simp_rw [← inner_gradient_left]
            exact hqm.inner (𝕜 := ℝ)
              (((measurable_gradient (φ : Space (m + 1) → ℝ)).inner (𝕜 := ℝ) hqm).smul_const ν)
          exact hm1.sub hm2
        apply (continuousOn_const.integrableOn_compact hK
          (f := fun _ ↦ (3 / 2 : ℝ) * κ ^ 2 * |Cf|)).mono' hmeas_Q.aestronglyMeasurable
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK
        have hop : ‖fderiv ℝ (φ : Space (m + 1) → ℝ) x‖ ≤ |Cf| :=
          (hCf x hxK).trans (le_abs_self Cf)
        have h1 : ‖(‖q x‖ ^ 2 / 2) * fderiv ℝ (φ : Space (m + 1) → ℝ) x ν‖ ≤
            (κ ^ 2 / 2) * |Cf| := by
          rw [norm_mul, Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul (div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (hqb x) 2) (by norm_num))
            ((ContinuousLinearMap.le_opNorm _ _).trans (by rw [hν, mul_one]; exact hop))
            (norm_nonneg _) (by positivity)
        have h2 : ‖inner ℝ (q x) ((fderiv ℝ (φ : Space (m + 1) → ℝ) x (q x)) • ν)‖ ≤
            κ ^ 2 * |Cf| := by
          apply (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          rw [norm_smul, hν, mul_one]
          have hqx : ‖fderiv ℝ (φ : Space (m + 1) → ℝ) x (q x)‖ ≤ |Cf| * κ :=
            (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hop (hqb x) (norm_nonneg _) (abs_nonneg _))
          calc
            ‖q x‖ * ‖fderiv ℝ (φ : Space (m + 1) → ℝ) x (q x)‖ ≤ κ * (|Cf| * κ) :=
              mul_le_mul (hqb x) hqx (norm_nonneg _) hκ.le
            _ = κ ^ 2 * |Cf| := by ring
        dsimp only [Q_stress]
        exact (norm_sub_le _ _).trans (by linarith)
      rw [← integral_sub (hiQ _ (measurable_gradient _) hv_gb)
        (hiQ _ (measurable_gradient _) hW_gb)]
      have hpt (x : Space (m + 1)) (hxK : x ∈ K) :
          ‖Q_stress (gradient (v j)) x - Q_stress (gradient W_lim) x‖ ≤
            (3 * κ * |Cf|) * ‖gradient (v j) x - gradient W_lim x‖ := by
        let p := gradient (v j) x
        let q := gradient W_lim x
        let L := fderiv ℝ (φ : Space (m + 1) → ℝ) x
        have hL : ‖L‖ ≤ |Cf| := (hCf x hxK).trans (le_abs_self Cf)
        have hp : ‖p‖ ≤ κ := hv_gb x
        have hq : ‖q‖ ≤ κ := hW_gb x
        have hA : ‖(‖p‖ ^ 2 / 2 - ‖q‖ ^ 2 / 2) * L ν‖ ≤
            κ * |Cf| * ‖p - q‖ := by
          have hsq_diff : |‖p‖ ^ 2 - ‖q‖ ^ 2| ≤ 2 * κ * ‖p - q‖ := by
            have hf1 : ‖p‖ ^ 2 - ‖q‖ ^ 2 = (‖p‖ + ‖q‖) * (‖p‖ - ‖q‖) := by ring
            rw [hf1, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
            exact mul_le_mul (by linarith) (abs_norm_sub_norm_le p q)
              (abs_nonneg _) (by positivity)
          have hLν : ‖L ν‖ ≤ |Cf| :=
            (ContinuousLinearMap.le_opNorm L ν).trans (by rw [hν, mul_one]; exact hL)
          rw [norm_mul, Real.norm_eq_abs]
          have hhalf : |‖p‖ ^ 2 / 2 - ‖q‖ ^ 2 / 2| ≤ κ * ‖p - q‖ := by
            rw [show ‖p‖ ^ 2 / 2 - ‖q‖ ^ 2 / 2 = (‖p‖ ^ 2 - ‖q‖ ^ 2) / 2 by ring, abs_div]
            have h2abs : |(2 : ℝ)| = 2 := by norm_num
            rw [h2abs]
            linarith
          calc
            |‖p‖ ^ 2 / 2 - ‖q‖ ^ 2 / 2| * ‖L ν‖ ≤ (κ * ‖p - q‖) * |Cf| :=
              mul_le_mul hhalf hLν (norm_nonneg _) (by positivity)
            _ = κ * |Cf| * ‖p - q‖ := by ring
        have hB : ‖inner ℝ p ((L p) • ν) - inner ℝ q ((L q) • ν)‖ ≤
            2 * κ * |Cf| * ‖p - q‖ := by
          have hid : inner ℝ p ((L p) • ν) - inner ℝ q ((L q) • ν) =
              inner ℝ (p - q) ((L p) • ν) + inner ℝ q ((L (p - q)) • ν) := by
            simp only [real_inner_smul_right, inner_sub_left, map_sub]
            ring
          rw [hid]
          have hb1 : ‖inner ℝ (p - q) ((L p) • ν)‖ ≤ κ * |Cf| * ‖p - q‖ := by
            apply (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
            rw [norm_smul, hν, mul_one]
            have hLp : ‖L p‖ ≤ |Cf| * κ :=
              (ContinuousLinearMap.le_opNorm L p).trans
                (mul_le_mul hL hp (norm_nonneg _) (abs_nonneg _))
            calc
              ‖p - q‖ * ‖L p‖ ≤ ‖p - q‖ * (|Cf| * κ) :=
                mul_le_mul_of_nonneg_left hLp (norm_nonneg _)
              _ = κ * |Cf| * ‖p - q‖ := by ring
          have hb2 : ‖inner ℝ q ((L (p - q)) • ν)‖ ≤ κ * |Cf| * ‖p - q‖ := by
            apply (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
            rw [norm_smul, hν, mul_one]
            have hLpq : ‖L (p - q)‖ ≤ |Cf| * ‖p - q‖ :=
              (ContinuousLinearMap.le_opNorm L (p - q)).trans
                (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
            calc
              ‖q‖ * ‖L (p - q)‖ ≤ κ * (|Cf| * ‖p - q‖) :=
                mul_le_mul hq hLpq (norm_nonneg _) hκ.le
              _ = κ * |Cf| * ‖p - q‖ := by ring
          exact (norm_add_le _ _).trans (by linarith)
        have hrew : Q_stress (gradient (v j)) x - Q_stress (gradient W_lim) x =
            (‖p‖ ^ 2 / 2 - ‖q‖ ^ 2 / 2) * L ν -
              (inner ℝ p ((L p) • ν) - inner ℝ q ((L q) • ν)) := by
          dsimp only [Q_stress, p, q, L]
          ring
        rw [hrew]
        exact (norm_sub_le _ _).trans (by linarith)
      have hi_norm_diff : IntegrableOn (fun x ↦ ‖gradient (v j) x - gradient W_lim x‖) K := by
        apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ 2 * κ)).mono'
          ((measurable_gradient (v j)).sub (measurable_gradient W_lim)).norm.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le _ _).trans (by linarith [hv_gb x, hW_gb x])
      -- Cauchy-Schwarz via `sq_le_sq`: `(∫_K g) ^ 2 ≤ (∫_K g ^ 2) * vol(K)`
      have hcs : (∫ x in K, ‖gradient (v j) x - gradient W_lim x‖) ≤
          Real.sqrt ((∫ x in K, ‖gradient (v j) x - gradient W_lim x‖ ^ 2) * volume.real K) := by
        let I1 := ∫ x in K, ‖gradient (v j) x - gradient W_lim x‖
        let I2 := ∫ x in K, ‖gradient (v j) x - gradient W_lim x‖ ^ 2
        have hI1_nn : 0 ≤ I1 := integral_nonneg (fun _ ↦ norm_nonneg _)
        have hI2_nn : 0 ≤ I2 := integral_nonneg (fun _ ↦ sq_nonneg _)
        by_cases hvK : volume.real K = 0
        · have hμ0 : volume.restrict K = 0 := by
            rw [Measure.restrict_eq_zero]
            exact (measureReal_eq_zero_iff (h := hK.measure_lt_top.ne)).mp hvK
          have hI1_0 : I1 = 0 := by simp [I1, hμ0]
          change I1 ≤ Real.sqrt (I2 * volume.real K)
          rw [hI1_0, hvK, mul_zero, Real.sqrt_zero]
        · have hvK_pos : 0 < volume.real K :=
            lt_of_le_of_ne measureReal_nonneg (Ne.symm hvK)
          apply Real.le_sqrt_of_sq_le
          -- Young's inequality with `t = I1 / vol K` gives `2 * t * I1 - t ^ 2 * vol K ≤ I2`
          let t := I1 / volume.real K
          have hig_sq : IntegrableOn (fun x ↦ ‖gradient (v j) x - gradient W_lim x‖ ^ 2) K :=
            integrableOn_gradient_sub_sq_of_lipschitz (hv_lip j) hW_lip hK
          have hyoung : (∫ x in K, (2 * t * ‖gradient (v j) x - gradient W_lim x‖ - t ^ 2)) ≤ I2 := by
            apply setIntegral_mono_on
              ((hi_norm_diff.const_mul (2 * t)).sub (continuousOn_const.integrableOn_compact hK))
              hig_sq hK.measurableSet
            intro x _
            dsimp only [Pi.sub_apply]
            nlinarith [sq_nonneg (‖gradient (v j) x - gradient W_lim x‖ - t)]
          rw [integral_sub (hi_norm_diff.const_mul (2 * t))
            (continuousOn_const.integrableOn_compact hK), integral_const_mul,
            setIntegral_const, smul_eq_mul] at hyoung
          have ht_id : 2 * t * I1 - volume.real K * t ^ 2 = I1 ^ 2 / volume.real K := by
            dsimp only [t]
            field_simp [hvK_pos.ne']
            ring
          change I1 ^ 2 ≤ I2 * volume.real K
          rw [ht_id, div_le_iff₀ hvK_pos] at hyoung
          exact hyoung
      calc
        ‖∫ x in K, (Q_stress (gradient (v j)) x - Q_stress (gradient W_lim) x)‖ ≤
            ∫ x in K, ‖Q_stress (gradient (v j)) x - Q_stress (gradient W_lim) x‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ x in K, (3 * κ * |Cf|) * ‖gradient (v j) x - gradient W_lim x‖ := by
          apply setIntegral_mono_on
            (((hiQ _ (measurable_gradient _) hv_gb).sub
              (hiQ _ (measurable_gradient _) hW_gb)).norm)
            (hi_norm_diff.const_mul (3 * κ * |Cf|)) hK.measurableSet hpt
        _ = (3 * κ * |Cf|) * ∫ x in K, ‖gradient (v j) x - gradient W_lim x‖ :=
          integral_const_mul _ _
        _ ≤ (3 * κ * |Cf|) * Real.sqrt ((∫ x in K,
            ‖gradient (v j) x - gradient W_lim x‖ ^ 2) * volume.real K) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hmaj : Tendsto (fun j ↦ (3 * κ * |Cf|) * Real.sqrt ((∫ x in K,
        ‖gradient (v j) x - gradient W_lim x‖ ^ 2) * volume.real K)) atTop (𝓝 0) := by
      have hs := ((hgrad K hK).mul_const (volume.real K)).sqrt
      rw [zero_mul, Real.sqrt_zero] at hs
      simpa only [mul_zero] using hs.const_mul (3 * κ * |Cf|)
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hdiff_le hmaj
  -- Combine kinetic + potential limits and evaluate on the halfspace profile `W_lim`
  have hsum_eq (j : ℕ) :
      Q_stress (gradient (v j)) +
        (fun x ↦ {y : Space (m + 1) | 0 < V (r_seq j • y)}.indicator
          (fun y ↦ normalizedPotential f (V (r_seq j • y))) x *
          fderiv ℝ (φ : Space (m + 1) → ℝ) x ν) =
      fun x ↦ (‖gradient (v j) x‖ ^ 2 / 2 +
          {y : Space (m + 1) | 0 < V (r_seq j • y)}.indicator
            (fun y ↦ normalizedPotential f (V (r_seq j • y))) x) *
          fderiv ℝ (φ : Space (m + 1) → ℝ) x ν -
        inner ℝ (gradient (v j) x)
          ((fderiv ℝ (φ : Space (m + 1) → ℝ) x (gradient (v j) x)) • ν) := by
    funext x
    dsimp only [Pi.add_apply, Q_stress]
    ring
  have hlim_zero : (∫ x in K, Q_stress (gradient W_lim) x) +
      (∫ x in K, {y : Space (m + 1) | 0 < inner ℝ ν y}.indicator
        (fun _ ↦ normalizedPotential f 0) x *
        fderiv ℝ (φ : Space (m + 1) → ℝ) x ν) = 0 := by
    have ht_tot := ht_kin.add ht_pot
    have hz_seq : ∀ j, (∫ x in K, Q_stress (gradient (v j)) x) +
        (∫ x in K, {y : Space (m + 1) | 0 < V (r_seq j • y)}.indicator
          (fun y ↦ normalizedPotential f (V (r_seq j • y))) x *
          fderiv ℝ (φ : Space (m + 1) → ℝ) x ν) = 0 := by
      intro j
      have hv_gb (x : Space (m + 1)) : ‖gradient (v j) x‖ ≤ κ := by
        rw [gradient, LinearIsometryEquiv.norm_map]
        exact norm_fderiv_le_of_lipschitz ℝ (hv_lip j)
      have hi1 : IntegrableOn (Q_stress (gradient (v j))) K := by
        have hmeas_Q : Measurable (Q_stress (gradient (v j))) := by
          have hm1 : Measurable
              (fun x ↦ (‖gradient (v j) x‖ ^ 2 / 2) * fderiv ℝ (φ : Space (m + 1) → ℝ) x ν) :=
            ((((measurable_gradient (v j)).norm.pow_const 2).div_const 2).mul
              ((hφ_cd.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable)
          have hm2 : Measurable (fun x ↦ inner ℝ (gradient (v j) x)
              ((fderiv ℝ (φ : Space (m + 1) → ℝ) x (gradient (v j) x)) • ν)) := by
            simp_rw [← inner_gradient_left]
            exact (measurable_gradient (v j)).inner (𝕜 := ℝ)
              (((measurable_gradient (φ : Space (m + 1) → ℝ)).inner (𝕜 := ℝ)
                (measurable_gradient (v j))).smul_const ν)
          exact hm1.sub hm2
        apply (continuousOn_const.integrableOn_compact hK
          (f := fun _ ↦ (3 / 2 : ℝ) * κ ^ 2 * |Cf|)).mono' hmeas_Q.aestronglyMeasurable
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK
        have hop : ‖fderiv ℝ (φ : Space (m + 1) → ℝ) x‖ ≤ |Cf| :=
          (hCf x hxK).trans (le_abs_self Cf)
        have hb1 : ‖(‖gradient (v j) x‖ ^ 2 / 2) * fderiv ℝ (φ : Space (m + 1) → ℝ) x ν‖ ≤
            (κ ^ 2 / 2) * |Cf| := by
          rw [norm_mul, Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul (div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (hv_gb x) 2) (by norm_num))
            ((ContinuousLinearMap.le_opNorm _ _).trans (by rw [hν, mul_one]; exact hop))
            (norm_nonneg _) (by positivity)
        have hb2 : ‖inner ℝ (gradient (v j) x)
            ((fderiv ℝ (φ : Space (m + 1) → ℝ) x (gradient (v j) x)) • ν)‖ ≤ κ ^ 2 * |Cf| := by
          apply (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          rw [norm_smul, hν, mul_one]
          have hqx : ‖fderiv ℝ (φ : Space (m + 1) → ℝ) x (gradient (v j) x)‖ ≤ |Cf| * κ :=
            (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hop (hv_gb x) (norm_nonneg _) (abs_nonneg _))
          calc
            ‖gradient (v j) x‖ * ‖fderiv ℝ (φ : Space (m + 1) → ℝ) x (gradient (v j) x)‖ ≤
                κ * (|Cf| * κ) :=
              mul_le_mul (hv_gb x) hqx (norm_nonneg _) hκ.le
            _ = κ ^ 2 * |Cf| := by ring
        dsimp only [Q_stress]
        exact (norm_sub_le _ _).trans (by linarith)
      have hi2 : IntegrableOn (fun x ↦ {y : Space (m + 1) | 0 < V (r_seq j • y)}.indicator
          (fun y ↦ normalizedPotential f (V (r_seq j • y))) x *
          fderiv ℝ (φ : Space (m + 1) → ℝ) x ν) K := by
        have hV_sc : Continuous (fun y : Space (m + 1) ↦ V (r_seq j • y)) :=
          hV.continuous.comp ((continuous_const (y := r_seq j)).smul continuous_id)
        have hmeas_set : MeasurableSet {y : Space (m + 1) | 0 < V (r_seq j • y)} :=
          (isOpen_lt (continuous_const (y := (0 : ℝ))) hV_sc).measurableSet
        have hc_comp : Continuous (fun y : Space (m + 1) ↦
            normalizedPotential f (V (r_seq j • y))) :=
          h.normalizedPotential_continuousOn.comp_continuous hV_sc (fun y ↦ hval (r_seq j • y))
        apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ |Cw| * |Cf|)).mono'
          ((hc_comp.measurable.indicator hmeas_set).mul
            ((hφ_cd.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable
            ).aestronglyMeasurable
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK
        have hfd_le : ‖fderiv ℝ (φ : Space (m + 1) → ℝ) x ν‖ ≤ |Cf| :=
          (ContinuousLinearMap.le_opNorm _ _).trans (by
            rw [hν, mul_one]; exact (hCf x hxK).trans (le_abs_self Cf))
        dsimp only [Pi.mul_apply]
        rw [norm_mul]
        apply mul_le_mul _ hfd_le (norm_nonneg _) (abs_nonneg _)
        by_cases hp : 0 < V (r_seq j • x)
        · have hmem : x ∈ {y : Space (m + 1) | 0 < V (r_seq j • y)} := hp
          rw [indicator_of_mem hmem]; exact (hCw _ (hval _)).trans (le_abs_self Cw)
        · have hnmem : x ∉ {y : Space (m + 1) | 0 < V (r_seq j • y)} := hp
          rw [indicator_of_notMem hnmem, norm_zero]; exact abs_nonneg Cw
      rw [← integral_add hi1 hi2]
      have hcongr : (∫ a in K, Q_stress (gradient (v j)) a +
          {y : Space (m + 1) | 0 < V (r_seq j • y)}.indicator
            (fun y ↦ normalizedPotential f (V (r_seq j • y))) a *
            fderiv ℝ (φ : Space (m + 1) → ℝ) a ν) =
          ∫ x in K, ((‖gradient (v j) x‖ ^ 2 / 2 +
            {y : Space (m + 1) | 0 < V (r_seq j • y)}.indicator
              (fun y ↦ normalizedPotential f (V (r_seq j • y))) x) *
            fderiv ℝ (φ : Space (m + 1) → ℝ) x ν -
          inner ℝ (gradient (v j) x)
            ((fderiv ℝ (φ : Space (m + 1) → ℝ) x (gradient (v j) x)) • ν)) :=
        setIntegral_congr_fun hK.measurableSet (fun a _ ↦ congrFun (hsum_eq j) a)
      rw [hcongr]
      exact hstress_j j
    exact tendsto_nhds_unique ht_tot (tendsto_const_nhds.congr' (Eventually.of_forall
      (fun j ↦ (hz_seq j).symm)))
  -- Compute `∫_K Q_stress (gradient W_lim) x = ∫_K 1_{⟨ν,x⟩>0} (-c² / 2) ∂_ν φ`
  have hQ_lim_eq : (∫ x in K, Q_stress (gradient W_lim) x) =
      ∫ x in K, {y : Space (m + 1) | 0 < inner ℝ ν y}.indicator
        (fun _ ↦ -(c ^ 2 / 2)) x * fderiv ℝ (φ : Space (m + 1) → ℝ) x ν := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hnull_hyp] with x hne
    dsimp only [Q_stress, W_lim]
    rw [gradient_halfspace_linear_pos c hne]
    by_cases hp : 0 < inner ℝ ν x
    · have hmem : x ∈ {y : Space (m + 1) | 0 < inner ℝ ν y} := hp
      rw [indicator_of_mem hmem, indicator_of_mem hmem, norm_smul, hν, mul_one,
        Real.norm_of_nonneg hc_pos.le, map_smul, smul_eq_mul, real_inner_smul_left,
        real_inner_smul_right, real_inner_self_eq_norm_sq, hν]
      ring
    · have hnmem : x ∉ {y : Space (m + 1) | 0 < inner ℝ ν y} := hp
      rw [indicator_of_notMem hnmem, indicator_of_notMem hnmem]
      simp
  rw [hQ_lim_eq] at hlim_zero
  obtain ⟨Q_rot, hQ_rot⟩ := exists_linearIsometryEquiv_vertical hν
  rw [integral_positive_halfspace_indicator_test Q_rot hQ_rot hφ_cd hcφ hK.measurableSet
      hφ_supp (-(c ^ 2 / 2)),
    integral_positive_halfspace_indicator_test Q_rot hQ_rot hφ_cd hcφ hK.measurableSet
      hφ_supp (normalizedPotential f 0)] at hlim_zero
  -- Check that the plane trace `∫ y : Space m, φ (Q_rot (point y 0))` is strictly positive
  have htrace_pos : 0 < ∫ y : Space m, (φ : Space (m + 1) → ℝ) (Q_rot (point y 0)) := by
    let g_tr : Space m → ℝ := fun y ↦ (φ : Space (m + 1) → ℝ) (Q_rot (point y 0))
    have hpt0_cont : Continuous (fun y : Space m ↦ point y 0) :=
      pointContinuousLinearMap.continuous.comp (continuous_id.prodMk (continuous_const (y := (0 : ℝ))))
    have hg_cont : Continuous g_tr :=
      φ.continuous.comp (Q_rot.continuous.comp hpt0_cont)
    have hg_supp : HasCompactSupport g_tr := by
      apply (isCompact_closedBall (0 : Space m) 2).of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ isClosed_closedBall
      intro y hy
      rw [Function.mem_support] at hy
      rw [mem_closedBall, dist_zero_right]
      have hmem : Q_rot (point y 0) ∈ ball (0 : Space (m + 1)) φ.rOut := by
        rw [← φ.support_eq]
        exact Function.mem_support.mpr hy
      rw [mem_ball, dist_zero_right, Q_rot.norm_map, norm_point_zero] at hmem
      exact le_of_lt hmem
    have hg0 : g_tr 0 ≠ 0 := by
      dsimp only [g_tr]
      have hp0 : point (0 : Space m) 0 = 0 := by
        ext i; refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point]
      rw [hp0, map_zero, φ.one_of_mem_closedBall (mem_closedBall_self φ.rIn_pos.le)]
      norm_num
    exact integral_pos_of_integrable_nonneg_nonzero hg_cont
      (hg_cont.integrable_of_hasCompactSupport hg_supp) (fun _ ↦ φ.nonneg) hg0
  have hpot_eq : c ^ 2 / 2 = normalizedPotential f 0 := by nlinarith
  have hk_sq := hr.kappa_sq_eq_twice_potential h
  have hc_sq : c ^ 2 = κ ^ 2 := by linarith
  nlinarith [hc_pos, h.kappa_pos]

/-- **Full-family normal slope at an exterior zero-ball contact (TB6.3)**:
If `V` is a physical translation limit with `V 0 = 0`, `0 ∈ closure {x | 0 < V x}`, and
`ball (-(R • ν)) R ⊆ {x | V x = 0}` (`‖ν‖ = 1`, `0 < R`), then
`V (s • ν) / s → κ` as `s → 0⁺`. -/
theorem RigidityHypotheses.exterior_zero_ball_normal_slope
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ R : ℝ}
    {ν : Space (m + 1)} {p_seq : ℕ → Space (m + 1)}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hν : ‖ν‖ = 1) (hR : 0 < R)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V atTop K)
    (hV0 : V 0 = 0) (hcl : (0 : Space (m + 1)) ∈ closure {x | 0 < V x})
    (hzero_ball : ball (-(R • ν)) R ⊆ {x | V x = 0}) :
    Tendsto (fun s : ℝ ↦ V (s • ν) / s) (𝓝[>] 0) (𝓝 κ) := by
  have hpointV (x : Space (m + 1)) :
      Tendsto (fun j ↦ zeroExtension g u (p_seq j + x)) atTop (𝓝 (V x)) :=
    (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hpointV x).dist (hpointV y))
      (Eventually.of_forall (fun j ↦ by
        simpa only [dist_add_left] using
          (hr.zeroExtension_lipschitzWith h).dist_le_mul (p_seq j + x) (p_seq j + y)))
  have hval (x : Space (m + 1)) : V x ∈ Icc 0 1 :=
    ⟨ge_of_tendsto (hpointV x) (Eventually.of_forall (fun _ ↦ h.zeroExtension_nonneg _)),
      le_of_tendsto (hpointV x) (Eventually.of_forall (fun _ ↦ (hr.zeroExtension_lt_one _).le))⟩
  rw [tendsto_iff_seq_tendsto]
  intro r_seq hr_mem
  by_contra hnot
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hfar⟩ := hnot
  -- Extract a subsequence `s_seq` along which `dist (V (s_seq j • ν) / s_seq j) κ ≥ ε`
  have hex_sub : ∃ ψ_sub : ℕ → ℕ, StrictMono ψ_sub ∧
      ∀ j, ε ≤ dist (V (r_seq (ψ_sub j) • ν) / r_seq (ψ_sub j)) κ := by
    choose N hN using hfar
    let ψ_sub : ℕ → ℕ := fun j ↦ Nat.recOn j (N 0) (fun _ prev ↦ N (prev + 1))
    refine ⟨ψ_sub, strictMono_nat_of_lt_succ (fun j ↦ ?_), fun j ↦ ?_⟩
    · dsimp only [ψ_sub]
      exact Nat.lt_of_succ_le (hN (Nat.recOn j (N 0) (fun _ prev ↦ N (prev + 1)) + 1)).1
    · cases j with
      | zero => exact (hN 0).2
      | succ k => exact (hN _).2
  obtain ⟨ψ_sub, hψ_sub, hdist_ge⟩ := hex_sub
  let s_seq : ℕ → ℝ := fun j ↦ r_seq (ψ_sub j)
  have hr_lim : Tendsto r_seq atTop (𝓝 0) :=
    (tendsto_nhdsWithin_iff.mp hr_mem).1
  have hr_pos_ev : ∀ᶠ j in atTop, 0 < r_seq j :=
    (tendsto_nhdsWithin_iff.mp hr_mem).2
  have hs_pos_ev : ∀ᶠ j in atTop, 0 < s_seq j :=
    hψ_sub.tendsto_atTop.eventually hr_pos_ev
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp hs_pos_ev
  -- Shift by `J₀` so every scale is strictly positive
  let t_seq : ℕ → ℝ := fun j ↦ s_seq (j + J₀)
  have ht_pos (j : ℕ) : 0 < t_seq j := hJ₀ (j + J₀) (Nat.le_add_left J₀ j)
  have ht_lim : Tendsto t_seq atTop (𝓝 0) :=
    (hr_lim.comp hψ_sub.tendsto_atTop).comp (tendsto_add_atTop_nat J₀)
  obtain ⟨φ_b, W_lim, hφ_b, hW, _, hW0, hW_homog, hWlim, hnondeg, _, htrunc, hgrad⟩ :=
    hr.exists_oneHomogeneous_microscopic_blowup_limit h hlim hV0 hcl ht_pos ht_lim
  have hW_zero_half := microscopic_blowup_zero_on_nonpos_halfspace hν hR hzero_ball
    (fun j ↦ ht_pos (φ_b j)) (ht_lim.comp hφ_b.tendsto_atTop) hW.continuous hWlim
  obtain ⟨c, ⟨hc_pos, hc_le⟩, hform⟩ :=
    halfspace_oneHomogeneous_eq_linear_pos h.kappa_pos hν hW hW0 hW_zero_half hW_homog
      hnondeg htrunc
  have hW_eq : W_lim = fun x ↦ c * max (inner ℝ ν x) 0 := funext hform
  rw [hW_eq] at hWlim hgrad
  have hc_eq : c = κ :=
    hr.halfspace_linear_pos_slope_eq_kappa h hν hR hc_pos hc_le hV hval hV0 hzero_ball hlim
      (fun j ↦ ht_pos (φ_b j)) (ht_lim.comp hφ_b.tendsto_atTop) hWlim hgrad
  have hpt_ν : Tendsto (fun j ↦ V (t_seq (φ_b j) • ν) / t_seq (φ_b j)) atTop (𝓝 κ) := by
    have ht := (hWlim {ν} isCompact_singleton).tendsto_at (mem_singleton ν)
    simpa only [hc_eq, real_inner_self_eq_norm_sq, hν, one_pow, max_eq_left zero_le_one,
      mul_one] using ht
  obtain ⟨j₁, hj₁⟩ := Metric.tendsto_atTop.mp hpt_ν ε hε
  exact (not_lt_of_ge (hdist_ge (φ_b j₁ + J₀))) (hj₁ j₁ le_rfl)

/-! ### TB7: Weak equation for Lipschitz interior tests and annular Hopf exclusion -/

/-- A physical translation limit satisfies its weak equation against every compactly supported
locally Lipschitz test function supported strictly inside its positive phase `{x | 0 < V_tilde x}`. -/
theorem RigidityHypotheses.physical_translation_limit_positive_lipschitz_test
    {m : ℕ} {g : Space m → ℝ} {u V_tilde ψ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    {p_seq : ℕ → Space (m + 1)}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hVt : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V_tilde)
    (hVt_val : ∀ x, V_tilde x ∈ Icc 0 1)
    (hVt_lim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V_tilde atTop K)
    (hψ : LocallyLipschitz ψ) (hc : HasCompactSupport ψ)
    (hsub : tsupport ψ ⊆ {x | 0 < V_tilde x}) :
    (∫ x, inner ℝ (gradient V_tilde x) (gradient ψ x) - f (V_tilde x) * ψ x) = 0 := by
  have hopen : IsOpen {x | 0 < V_tilde x} := isOpen_lt continuous_const hVt.continuous
  rcases (tsupport ψ).eq_empty_or_nonempty with hemp | hne
  · apply integral_eq_zero_of_ae
    refine Eventually.of_forall (fun x ↦ ?_)
    have hn : x ∉ tsupport ψ := by rw [hemp]; exact notMem_empty x
    simp [gradient, fderiv_of_notMem_tsupport ℝ hn, image_eq_zero_of_notMem_tsupport hn]
  -- Thicken `tsupport ψ` inside `{x | 0 < V_tilde x}` by a positive Euclidean `infDist` margin `δ`
  have hex_δ : ∃ δ : ℝ, 0 < δ ∧
      {y : Space (m + 1) | Metric.infDist y (tsupport ψ) ≤ δ} ⊆ {x | 0 < V_tilde x} := by
    have hcompl_closed : IsClosed ({x | 0 < V_tilde x})ᶜ := hopen.isClosed_compl
    rcases ({x | 0 < V_tilde x})ᶜ.eq_empty_or_nonempty with hc_emp | hc_ne
    · refine ⟨1, zero_lt_one, ?_⟩
      have huniv : {x | 0 < V_tilde x} = univ := compl_empty_iff.mp hc_emp
      rw [huniv]
      exact subset_univ _
    · obtain ⟨z_min, hz_min, hmin⟩ := hc.exists_isMinOn hne
        (Metric.continuous_infDist_pt ({x | 0 < V_tilde x})ᶜ).continuousOn
      have hd_pos : 0 < Metric.infDist z_min ({x | 0 < V_tilde x})ᶜ :=
        (Metric.infDist_pos_iff_notMem_closure hc_ne).mp
          (by rw [hcompl_closed.closure_eq]; exact fun hmem ↦ hmem (hsub hz_min))
      refine ⟨Metric.infDist z_min ({x | 0 < V_tilde x})ᶜ / 2, half_pos hd_pos, ?_⟩
      intro y hy
      have hy_le : Metric.infDist y (tsupport ψ) ≤
          Metric.infDist z_min ({x | 0 < V_tilde x})ᶜ / 2 := hy
      by_contra hnot
      have hy_compl : y ∈ ({x | 0 < V_tilde x})ᶜ := hnot
      obtain ⟨w, hw, hwy⟩ := hc.exists_infDist_eq_dist hne y
      have h1 : Metric.infDist w ({x | 0 < V_tilde x})ᶜ ≤ dist w y :=
        Metric.infDist_le_dist_of_mem hy_compl
      have h2 : Metric.infDist z_min ({x | 0 < V_tilde x})ᶜ ≤
          Metric.infDist w ({x | 0 < V_tilde x})ᶜ := hmin hw
      rw [dist_comm] at hwy
      linarith
  obtain ⟨δ, hδ, hthick⟩ := hex_δ
  obtain ⟨R_b, hR_b⟩ := hc.isBounded.subset_closedBall (0 : Space (m + 1))
  let K := closedBall (0 : Space (m + 1)) (R_b + 1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hψK : tsupport ψ ⊆ K := hR_b.trans (closedBall_subset_closedBall (by linarith))
  -- Decompose `ψ = max ψ 0 - max (-ψ) 0` into nonnegative compactly supported Lipschitz parts
  let ψ_pos : Space (m + 1) → ℝ := fun x ↦ max (ψ x) 0
  let ψ_neg : Space (m + 1) → ℝ := fun x ↦ max (-ψ x) 0
  have hpart (θ : Space (m + 1) → ℝ) (hθ : LocallyLipschitz θ)
      (hcθ : HasCompactSupport θ) (hθ0 : ∀ x, 0 ≤ θ x)
      (hθ_sub : tsupport θ ⊆ tsupport ψ) :
      (∫ x, inner ℝ (gradient V_tilde x) (gradient θ x) - f (V_tilde x) * θ x) = 0 := by
    obtain ⟨B, hB⟩ := hcθ.exists_bound_of_continuous hθ.continuous
    have hθval (x : Space (m + 1)) : θ x ∈ Icc 0 B :=
      ⟨hθ0 x, (le_abs_self _).trans (hB x)⟩
    have hmval (j : ℕ) (x : Space (m + 1)) :=
      normalizedMollify_mem_Icc_of_bounds hθ.continuous hθval j x
    obtain ⟨Cg, hCg⟩ := normalizedMollify_gradient_bound_of_locallyLipschitz hθ hK
    obtain ⟨Af, hAf⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
    have hf_cont : Continuous (fun x ↦ f (V_tilde x)) :=
      h.reaction_contDiffOn.continuousOn.comp_continuous hVt.continuous
        (fun x ↦ (hVt_val x).1)
    have hVt_gb (x : Space (m + 1)) : ‖gradient V_tilde x‖ ≤ κ := by
      rw [gradient, LinearIsometryEquiv.norm_map]
      exact norm_fderiv_le_of_lipschitz ℝ hVt
    have hθ_R : tsupport θ ⊆ closedBall 0 R_b := hθ_sub.trans hR_b
    have hmK (j : ℕ) : tsupport (normalizedMollify θ j) ⊆ K :=
      normalizedMollify_tsupport_subset hθ_R j
    have hlim_m : Tendsto (fun j ↦ ∫ x in K,
        inner ℝ (gradient V_tilde x) (gradient (normalizedMollify θ j) x) -
          f (V_tilde x) * normalizedMollify θ j x) atTop
        (𝓝 (∫ x in K, inner ℝ (gradient V_tilde x) (gradient θ x) -
          f (V_tilde x) * θ x)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ ↦ κ * Cg + |Af| * B)
      · intro j
        exact (((measurable_gradient V_tilde).inner (𝕜 := ℝ) (measurable_gradient _)).sub
          (hf_cont.measurable.mul
            (normalizedMollify_contDiff hθ.continuous j).continuous.measurable)
          ).aestronglyMeasurable
      · exact continuousOn_const.integrableOn_compact hK
      · intro j
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK
        apply (norm_sub_le _ _).trans
        apply add_le_add
        · exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
            (mul_le_mul (hVt_gb x) (hCg j x hxK) (norm_nonneg _) h.kappa_pos.le)
        · rw [norm_mul, Real.norm_of_nonneg (hmval j x).1]
          exact mul_le_mul ((hAf _ (hVt_val x)).trans (le_abs_self Af)) (hmval j x).2
            (hmval j x).1 (abs_nonneg Af)
      · filter_upwards [ae_restrict_of_ae
          (normalizedMollify_gradient_tendsto_ae_of_locallyLipschitz hθ)] with x hx
        exact (tendsto_const_nhds.inner hx).sub
          (tendsto_const_nhds.mul (normalizedMollify_tendsto hθ.continuous x))
    -- For `1 / (j + 1) ≤ δ`, `tsupport (normalizedMollify θ j) ⊆ cthickening δ (tsupport ψ)`
    obtain ⟨J, hJ⟩ := exists_nat_gt (1 / δ)
    have hev_zero : ∀ᶠ j in atTop,
        (∫ x in K, inner ℝ (gradient V_tilde x) (gradient (normalizedMollify θ j) x) -
          f (V_tilde x) * normalizedMollify θ j x) = 0 := by
      filter_upwards [eventually_ge_atTop J] with j hj
      let φj := normalizedMollify θ j
      have hφj_cd : ContDiff ℝ 2 φj :=
        (normalizedMollify_contDiff hθ.continuous j).of_le (by simp)
      have hcφj : HasCompactSupport φj :=
        hK.of_isClosed_subset (isClosed_tsupport _) (hmK j)
      have hr_le : 1 / ((j : ℝ) + 1) ≤ δ := by
        have hgt : 1 / δ < (j : ℝ) + 1 := by
          have h1 : (J : ℝ) ≤ j := Nat.cast_le.mpr hj
          linarith
        exact (div_le_iff₀ (by positivity)).mpr ((div_lt_iff₀ hδ).mp hgt |>.le.trans
          (by rw [mul_comm]))
      have hsupp_j : tsupport φj ⊆ {x | 0 < V_tilde x} := by
        apply Subset.trans _ hthick
        apply closure_minimal _ (isClosed_le (Metric.continuous_infDist_pt _) continuous_const)
        intro x hx
        rw [Function.mem_support] at hx
        -- If `φj x ≠ 0`, some `y ∈ ball 0 (1 / (j + 1))` has `θ (x - y) ≠ 0`
        have hex_y : ∃ y ∈ ball (0 : Space (m + 1)) (1 / ((j : ℝ) + 1)),
            θ (x - y) ≠ 0 := by
          by_contra hall
          push Not at hall
          have hm0 : mollify θ j x = 0 := by
            unfold mollify
            change (∫ y, (averagingBump (m + 1) j).normed volume y * θ (x - y)) = 0
            apply integral_eq_zero_of_ae
            refine Eventually.of_forall (fun y ↦ ?_)
            dsimp only [Pi.zero_apply]
            by_cases hy : y ∈ ball (0 : Space (m + 1)) (averagingBump (m + 1) j).rOut
            · rw [hall y hy, mul_zero]
            · have hk0 : (averagingBump (m + 1) j).normed volume y = 0 :=
                Function.notMem_support.mp
                  (by simpa [(averagingBump (m + 1) j).support_normed_eq] using hy)
              rw [hk0, zero_mul]
          exact hx (by simp [φj, normalizedMollify, hm0])
        obtain ⟨y, hy, hθxy⟩ := hex_y
        have hmem_ts : x - y ∈ tsupport ψ :=
          hθ_sub (subset_tsupport θ (Function.mem_support.mpr hθxy))
        refine (Metric.infDist_le_dist_of_mem hmem_ts).trans ?_
        rw [dist_eq_norm, sub_sub_cancel]
        have hny : ‖y‖ < 1 / ((j : ℝ) + 1) := by
          simpa only [mem_ball, dist_zero_right] using hy
        exact hny.le.trans hr_le
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
        have hn : x ∉ tsupport φj := fun hh ↦ hx (hmK j hh)
        change inner ℝ (gradient V_tilde x) (gradient φj x) - f (V_tilde x) * φj x = 0
        simp [gradient, fderiv_of_notMem_tsupport ℝ hn, image_eq_zero_of_notMem_tsupport hn])]
      have his : Integrable (fun x ↦ f (V_tilde x) * φj x) :=
        (hf_cont.mul hφj_cd.continuous).integrable_of_hasCompactSupport hcφj.mul_left
      have hig : Integrable (fun x ↦ inner ℝ (gradient V_tilde x) (gradient φj x)) := by
        simpa using integrable_weak_residual_of_locallyLipschitz_test
          (measurable_gradient V_tilde) (measurable_const (a := (0 : ℝ))) hVt_gb
          (fun _ ↦ le_rfl) (hφj_cd.of_le (by norm_num)).locallyLipschitz hcφj
      have hd := hr.physical_translation_limit_distributional_equation h hVt.continuous hVt_val
        hVt_lim hφj_cd hcφj hsupp_j
      rw [integral_mul_laplacian_eq_neg_inner_gradient_of_locallyLipschitz
        hVt.locallyLipschitz hVt_val hφj_cd hcφj] at hd
      rw [integral_sub hig his]
      linarith
    have hK_zero := tendsto_nhds_unique hlim_m
      (tendsto_const_nhds.congr' (hev_zero.mono (fun _ hj ↦ hj.symm)))
    rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      have hn : x ∉ tsupport θ := fun hh ↦ hx ((hθ_sub.trans hψK) hh)
      simp [gradient, fderiv_of_notMem_tsupport ℝ hn, image_eq_zero_of_notMem_tsupport hn])]
      at hK_zero
  have hpos_sub : tsupport ψ_pos ⊆ tsupport ψ :=
    tsupport_comp_subset (g := fun t : ℝ ↦ max t 0) (by simp) ψ
  have hneg_sub : tsupport ψ_neg ⊆ tsupport ψ :=
    tsupport_comp_subset (g := fun t : ℝ ↦ max (-t) 0) (by simp) ψ
  have hpos_lip : LocallyLipschitz ψ_pos := locallyLipschitz_posPart hψ
  have hneg_lip : LocallyLipschitz ψ_neg := locallyLipschitz_posPart hψ.neg
  have hc_pos : HasCompactSupport ψ_pos := hc.of_isClosed_subset (isClosed_tsupport _) hpos_sub
  have hc_neg : HasCompactSupport ψ_neg := hc.of_isClosed_subset (isClosed_tsupport _) hneg_sub
  have h0_pos := hpart ψ_pos hpos_lip hc_pos (fun _ ↦ le_max_right _ _) hpos_sub
  have h0_neg := hpart ψ_neg hneg_lip hc_neg (fun _ ↦ le_max_right _ _) hneg_sub
  obtain ⟨Af, hAf⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
  have hf_cont : Continuous (fun x ↦ f (V_tilde x)) :=
    h.reaction_contDiffOn.continuousOn.comp_continuous hVt.continuous (fun x ↦ (hVt_val x).1)
  have hVt_gb (x : Space (m + 1)) : ‖gradient V_tilde x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hVt
  have hi_pos := integrable_weak_residual_of_locallyLipschitz_test (measurable_gradient V_tilde)
    hf_cont.measurable hVt_gb (fun x ↦ hAf _ (hVt_val x)) hpos_lip hc_pos
  have hi_neg := integrable_weak_residual_of_locallyLipschitz_test (measurable_gradient V_tilde)
    hf_cont.measurable hVt_gb (fun x ↦ hAf _ (hVt_val x)) hneg_lip hc_neg
  have hae_split : ∀ᵐ x,
      inner ℝ (gradient V_tilde x) (gradient ψ x) - f (V_tilde x) * ψ x =
        (inner ℝ (gradient V_tilde x) (gradient ψ_pos x) - f (V_tilde x) * ψ_pos x) -
          (inner ℝ (gradient V_tilde x) (gradient ψ_neg x) - f (V_tilde x) * ψ_neg x) := by
    have hae_p : ∀ᵐ x, DifferentiableAt ℝ ψ_pos x := by
      have he (n : ℕ) : ∀ᵐ x, x ∈ closedBall (0 : Space (m + 1)) (n + 1) →
          DifferentiableWithinAt ℝ ψ_pos (closedBall 0 (n + 1)) x := by
        obtain ⟨L, hL⟩ := hpos_lip.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
          (isCompact_closedBall 0 (n + 1))
        exact hL.ae_differentiableWithinAt_of_mem
      filter_upwards [ae_all_iff.mpr he] with x hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      have hb : x ∈ ball (0 : Space (m + 1)) (n + 1) := by
        simp only [mem_ball, dist_zero_right]; linarith
      exact (hx n (ball_subset_closedBall hb)).differentiableAt (closedBall_mem_nhds_of_mem hb)
    have hae_n : ∀ᵐ x, DifferentiableAt ℝ ψ_neg x := by
      have he (n : ℕ) : ∀ᵐ x, x ∈ closedBall (0 : Space (m + 1)) (n + 1) →
          DifferentiableWithinAt ℝ ψ_neg (closedBall 0 (n + 1)) x := by
        obtain ⟨L, hL⟩ := hneg_lip.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
          (isCompact_closedBall 0 (n + 1))
        exact hL.ae_differentiableWithinAt_of_mem
      filter_upwards [ae_all_iff.mpr he] with x hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      have hb : x ∈ ball (0 : Space (m + 1)) (n + 1) := by
        simp only [mem_ball, dist_zero_right]; linarith
      exact (hx n (ball_subset_closedBall hb)).differentiableAt (closedBall_mem_nhds_of_mem hb)
    filter_upwards [hae_p, hae_n] with x hdp hdn
    have hψ_id : ψ = fun y ↦ ψ_pos y - ψ_neg y := by
      funext y
      dsimp only [ψ_pos, ψ_neg]
      by_cases hy : 0 ≤ ψ y
      · rw [max_eq_left hy, max_eq_right (neg_nonpos.mpr hy), sub_zero]
      · push Not at hy
        rw [max_eq_right hy.le, max_eq_left (neg_nonneg.mpr hy.le), zero_sub, neg_neg]
    have hg_sub : gradient ψ x = gradient ψ_pos x - gradient ψ_neg x := by
      rw [hψ_id]
      simp only [gradient, fderiv_fun_sub hdp hdn, map_sub]
    have hv_sub : ψ x = ψ_pos x - ψ_neg x := congrFun hψ_id x
    rw [hg_sub, hv_sub, inner_sub_right]
    ring
  rw [integral_congr_ae hae_split, integral_sub hi_pos hi_neg, h0_pos, h0_neg, sub_zero]

/-- **Exclusion of opposite phase balls with strictly positive difference (TB7)**:
Suppose `V` and `V_tilde` are physical translation limits vanishing at `0` with `V ≤ V_tilde`
everywhere, `0 ∈ closure {x | 0 < V x}`, `ball (-(r • ν)) r ⊆ {x | V x = 0}`,
`ball (r • ν) r ⊆ {x | 0 < V_tilde x}`, and `V x < V_tilde x` for all `x ∈ ball (r • ν) r`
(`‖ν‖ = 1`, `0 < r`). Then `False` holds. -/
theorem RigidityHypotheses.false_of_opposite_phase_balls_and_positive_diff
    {m : ℕ} {g : Space m → ℝ} {u V V_tilde : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ r : ℝ}
    {ν : Space (m + 1)} {p_seq q_seq : ℕ → Space (m + 1)}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hν : ‖ν‖ = 1) (hr_pos : 0 < r)
    (hV_lim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V atTop K)
    (hVt_lim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (q_seq j + x)) V_tilde atTop K)
    (hV0 : V 0 = 0) (hVt0 : V_tilde 0 = 0)
    (hcl : (0 : Space (m + 1)) ∈ closure {x | 0 < V x})
    (horder : ∀ x, V x ≤ V_tilde x)
    (hzero_ball : ball (-(r • ν)) r ⊆ {x | V x = 0})
    (hpos_ball : ball (r • ν) r ⊆ {x | 0 < V_tilde x})
    (hstrict_ball : ∀ x ∈ ball (r • ν) r, V x < V_tilde x) :
    False := by
  have hpointV (x : Space (m + 1)) :
      Tendsto (fun j ↦ zeroExtension g u (p_seq j + x)) atTop (𝓝 (V x)) :=
    (hV_lim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hpointVt (x : Space (m + 1)) :
      Tendsto (fun j ↦ zeroExtension g u (q_seq j + x)) atTop (𝓝 (V_tilde x)) :=
    (hVt_lim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hpointV x).dist (hpointV y))
      (Eventually.of_forall (fun j ↦ by
        simpa only [dist_add_left] using
          (hr.zeroExtension_lipschitzWith h).dist_le_mul (p_seq j + x) (p_seq j + y)))
  have hVt : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V_tilde := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hpointVt x).dist (hpointVt y))
      (Eventually.of_forall (fun j ↦ by
        simpa only [dist_add_left] using
          (hr.zeroExtension_lipschitzWith h).dist_le_mul (q_seq j + x) (q_seq j + y)))
  have hV_val (x : Space (m + 1)) : V x ∈ Icc 0 1 :=
    ⟨ge_of_tendsto (hpointV x) (Eventually.of_forall (fun _ ↦ h.zeroExtension_nonneg _)),
      le_of_tendsto (hpointV x) (Eventually.of_forall (fun _ ↦ (hr.zeroExtension_lt_one _).le))⟩
  have hVt_val (x : Space (m + 1)) : V_tilde x ∈ Icc 0 1 :=
    ⟨ge_of_tendsto (hpointVt x) (Eventually.of_forall (fun _ ↦ h.zeroExtension_nonneg _)),
      le_of_tendsto (hpointVt x) (Eventually.of_forall (fun _ ↦ (hr.zeroExtension_lt_one _).le))⟩
  -- Step 1: Normal slope of `V` at `0` is `κ` by TB6
  have hslope_V := hr.exterior_zero_ball_normal_slope h hν hr_pos hV_lim hV0 hcl hzero_ball
  -- Step 2: Lipschitz constant `Lf` of `f` on `[0, 1]` and barrier parameter `α` on `[r / 2, r]`
  obtain ⟨Lf, hLf⟩ := (h.reaction_contDiffOn.mono Icc_subset_Ici_self).exists_lipschitzOnWith
    one_ne_zero (convex_Icc 0 1) isCompact_Icc
  let M : ℝ := (Lf : ℝ) + 1
  have hM_pos : 0 < M := by dsimp only [M]; positivity
  obtain ⟨α, hα, hparam⟩ :=
    exists_annularBarrier_parameter (E := Space (m + 1)) (half_pos hr_pos) hM_pos.le
  let c_in : Space (m + 1) := r • ν
  -- Minimum of `V_tilde - V` on the inner closed ball `closedBall c_in (r / 2) ⊆ ball c_in r`
  have hcb_sub : closedBall c_in (r / 2) ⊆ ball c_in r :=
    closedBall_subset_ball (half_lt_self hr_pos)
  obtain ⟨x_min, hx_min, hmin⟩ := (isCompact_closedBall c_in (r / 2)).exists_isMinOn
    (nonempty_closedBall.mpr (half_pos hr_pos).le)
    (hVt.continuous.sub hV.continuous).continuousOn
  let ε : ℝ := V_tilde x_min - V x_min
  have hε_pos : 0 < ε := sub_pos.mpr (hstrict_ball x_min (hcb_sub hx_min))
  -- Step 3: Annular comparison `ε * annularBarrier c_in α r x ≤ V_tilde x - V x` on `ball c_in r`
  have hann_le : ∀ x ∈ ball c_in r,
      ε * annularBarrier c_in α r x ≤ V_tilde x - V x := by
    intro x₀ hx₀
    by_contra hlt_x₀
    push Not at hlt_x₀
    let δ : ℝ := (ε * annularBarrier c_in α r x₀ - (V_tilde x₀ - V x₀)) / 2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    let β : Space (m + 1) → ℝ := fun x ↦ ε * annularBarrier c_in α r x
    let w : Space (m + 1) → ℝ := fun x ↦ V_tilde x - V x - β x + δ
    let ψ : Space (m + 1) → ℝ := fun x ↦ max (-w x) 0
    have hβ_cd : ContDiff ℝ (⊤ : ℕ∞) β := contDiff_const.mul (contDiff_annularBarrier c_in α r)
    have hw_lip : LocallyLipschitz w :=
      ((hVt.locallyLipschitz.sub hV.locallyLipschitz).sub
        (hβ_cd.of_le (by simp)).locallyLipschitz).add
          ((contDiff_const (c := δ) : ContDiff ℝ 1 (fun _ : Space (m + 1) ↦ δ)).locallyLipschitz)
    have hψ_lip : LocallyLipschitz ψ := locallyLipschitz_posPart hw_lip.neg
    -- Support of `ψ` is compactly contained in the open annulus `{r / 2 < ‖x - c_in‖ < r}`
    let A_ann : Set (Space (m + 1)) := {x | r / 2 < ‖x - c_in‖ ∧ ‖x - c_in‖ < r}
    have hψ_supp : tsupport ψ ⊆ A_ann := by
      have hclosed_le : IsClosed {x | w x ≤ 0} := isClosed_le hw_lip.continuous continuous_const
      have hsub_le : tsupport ψ ⊆ {x | w x ≤ 0} := by
        apply closure_minimal _ hclosed_le
        intro x hx
        rw [Function.mem_support] at hx
        by_contra hpos_w
        exact hx (max_eq_right (neg_nonpos.mpr (not_le.mp hpos_w).le))
      refine hsub_le.trans (fun x hx ↦ ⟨?_, ?_⟩)
      · by_contra hle_in
        push Not at hle_in
        have hx_cb : x ∈ closedBall c_in (r / 2) := by
          simpa only [mem_closedBall, dist_eq_norm] using hle_in
        have h1 : ε ≤ V_tilde x - V x := hmin hx_cb
        have h2 : β x < ε := by
          dsimp only [β]
          exact mul_lt_of_lt_one_right hε_pos (annularBarrier_lt_one c_in x hα.le r)
        have hwx : V_tilde x - V x - β x + δ ≤ 0 := hx
        linarith
      · by_contra hge_out
        push Not at hge_out
        have hb_np : annularBarrier c_in α r x ≤ 0 :=
          annularBarrier_nonpos hα.le hr_pos.le hge_out
        have h1 : 0 ≤ V_tilde x - V x := sub_nonneg.mpr (horder x)
        have h2 : β x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε_pos.le hb_np
        have hwx : V_tilde x - V x - β x + δ ≤ 0 := hx
        linarith
    have hA_sub_ball : A_ann ⊆ ball c_in r := fun x hx ↦ by
      simpa only [mem_ball, dist_eq_norm] using hx.2
    have hcψ : HasCompactSupport ψ :=
      (isCompact_closedBall c_in r).of_isClosed_subset (isClosed_tsupport _)
        ((hψ_supp.trans hA_sub_ball).trans ball_subset_closedBall)
    -- Test `V` and `V_tilde` against `ψ`
    have htest_V := hr.physical_translation_limit_lipschitz_test h hV hV_val hpointV
      hψ_lip hcψ (fun _ ↦ le_max_right _ _)
    have htest_Vt := hr.physical_translation_limit_positive_lipschitz_test h hVt hVt_val
      hVt_lim hψ_lip hcψ ((hψ_supp.trans hA_sub_ball).trans hpos_ball)
    -- Smooth test for `β`: integrate by parts on `Space (m + 1)` using a ball cutoff
    obtain ⟨Bψ, hBψ⟩ := hcψ.exists_bound_of_continuous hψ_lip.continuous
    have hψ_val (x : Space (m + 1)) : ψ x ∈ Icc 0 Bψ :=
      ⟨le_max_right _ _, (le_abs_self _).trans (hBψ x)⟩
    let θ_b : ContDiffBump c_in :=
      { rIn := r + 1
        rOut := r + 2
        rIn_pos := by linarith
        rIn_lt_rOut := by linarith }
    let X_β : Space (m + 1) → Space (m + 1) :=
      fun x ↦ (θ_b : Space (m + 1) → ℝ) x • gradient β x
    have hβ_cd2 : ContDiff ℝ 2 β := hβ_cd.of_le (by simp)
    have hX_β : ContDiff ℝ 1 X_β := by
      have hgβ : ContDiff ℝ 1 (gradient β) := by
        unfold gradient
        exact (toDual ℝ (Space (m + 1))).symm.contDiff.comp (hβ_cd2.fderiv_right (by norm_num))
      exact θ_b.contDiff.smul hgβ
    have hcX_β : HasCompactSupport X_β := θ_b.hasCompactSupport.smul_right
    let b_std := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
    have hibp_β := integral_fieldDivergence_mul_eq_neg_inner_gradient_of_locallyLipschitz
      b_std hψ_lip hψ_val hX_β hcX_β
    have hβ_ibp : (∫ x, inner ℝ (gradient β x) (gradient ψ x)) =
        -∫ x, (Δ β) x * ψ x := by
      have hL : (∫ x, inner ℝ (gradient ψ x) (X_β x)) =
          ∫ x, inner ℝ (gradient β x) (gradient ψ x) := by
        apply integral_congr_ae
        refine Eventually.of_forall (fun x ↦ ?_)
        dsimp only [X_β]
        by_cases hx : x ∈ tsupport ψ
        · have hxb : x ∈ closedBall c_in (r + 1) := by
            have h1 : dist x c_in < r := hA_sub_ball (hψ_supp hx)
            rw [mem_closedBall]; linarith
          rw [θ_b.one_of_mem_closedBall hxb, one_smul, real_inner_comm]
        · simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
      have hR : (∫ x, ψ x * fieldDivergence b_std X_β x) = ∫ x, (Δ β) x * ψ x := by
        apply integral_congr_ae
        refine Eventually.of_forall (fun x ↦ ?_)
        dsimp only
        by_cases hx : x ∈ tsupport ψ
        · have hxb : x ∈ ball c_in (r + 1) := by
            have h1 : dist x c_in < r := hA_sub_ball (hψ_supp hx)
            rw [mem_ball]; linarith
          have hev : X_β =ᶠ[𝓝 x] gradient β := by
            filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
            dsimp only [X_β]
            rw [θ_b.one_of_mem_closedBall (ball_subset_closedBall hy), one_smul]
          have hdiv_eq : fieldDivergence b_std X_β x = (Δ β) x := by
            have hgβ_diff : DifferentiableAt ℝ (gradient β) x := by
              unfold gradient
              exact ((toDual ℝ (Space (m + 1))).symm.contDiff.comp
                (hβ_cd2.fderiv_right (by norm_num))).differentiable one_ne_zero x
            have hh := laplacian_eq_sum_gradient_derivative_of_differentiable hgβ_diff b_std
            rw [hh]
            unfold fieldDivergence
            refine Finset.sum_congr rfl (fun i _ ↦ ?_)
            rw [hev.fderiv_eq]
            exact real_inner_comm _ _
          rw [hdiv_eq, mul_comm]
        · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
      rw [← hL, ← hR, hibp_β, neg_neg]
    -- Subsolution sign of `β` on `tsupport ψ ⊆ A_ann`
    have hβ_sub_int : 0 ≤ -(∫ x, inner ℝ (gradient β x) (gradient ψ x)) -
        ∫ x, M * β x * ψ x := by
      rw [hβ_ibp, neg_neg]
      have hi1 : Integrable (fun x ↦ (Δ β) x * ψ x) :=
        ((continuous_laplacian_of_contDiff (hβ_cd.of_le (by simp))).mul
          hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
      have hi2 : Integrable (fun x ↦ M * β x * ψ x) :=
        ((continuous_const.mul hβ_cd.continuous).mul
          hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
      rw [← integral_sub hi1 hi2]
      apply integral_nonneg
      intro x
      dsimp only [Pi.sub_apply]
      by_cases hx : x ∈ tsupport ψ
      · have hxA := hψ_supp hx
        have hlap_β : (Δ β) x = ε * (Δ (annularBarrier c_in α r)) x := by
          change (Δ (ε • annularBarrier c_in α r)) x = _
          exact laplacian_smul ε (contDiff_annularBarrier c_in α r (n := 2)).contDiffAt
        have hsub_bar := annularBarrier_subsolution (R := r) hM_pos.le (half_pos hr_pos).le
          hxA.1.le hparam
        have hmul := mul_nonneg hε_pos.le hsub_bar
        have hrew : (Δ β) x * ψ x - M * β x * ψ x =
            (ε * ((Δ (annularBarrier c_in α r)) x - M * annularBarrier c_in α r x)) * ψ x := by
          dsimp only [β]
          rw [hlap_β]
          ring
        rw [hrew]
        exact mul_nonneg hmul (le_max_right _ _)
      · simp [image_eq_zero_of_notMem_tsupport hx]
    -- Reaction difference + `M * (V_tilde - V)` nonnegativity
    have hfV_cont : Continuous (fun x ↦ f (V x)) :=
      h.reaction_contDiffOn.continuousOn.comp_continuous hV.continuous (fun x ↦ (hV_val x).1)
    have hfVt_cont : Continuous (fun x ↦ f (V_tilde x)) :=
      h.reaction_contDiffOn.continuousOn.comp_continuous hVt.continuous (fun x ↦ (hVt_val x).1)
    have hV_gb (x : Space (m + 1)) : ‖gradient V x‖ ≤ κ := by
      rw [gradient, LinearIsometryEquiv.norm_map]; exact norm_fderiv_le_of_lipschitz ℝ hV
    have hVt_gb (x : Space (m + 1)) : ‖gradient V_tilde x‖ ≤ κ := by
      rw [gradient, LinearIsometryEquiv.norm_map]; exact norm_fderiv_le_of_lipschitz ℝ hVt
    have hig_V : Integrable (fun x ↦ inner ℝ (gradient V x) (gradient ψ x)) := by
      simpa using integrable_weak_residual_of_locallyLipschitz_test
        (measurable_gradient V) (measurable_const (a := (0 : ℝ))) hV_gb
        (fun _ ↦ le_rfl) hψ_lip hcψ
    have hig_Vt : Integrable (fun x ↦ inner ℝ (gradient V_tilde x) (gradient ψ x)) := by
      simpa using integrable_weak_residual_of_locallyLipschitz_test
        (measurable_gradient V_tilde) (measurable_const (a := (0 : ℝ))) hVt_gb
        (fun _ ↦ le_rfl) hψ_lip hcψ
    have hig_β : Integrable (fun x ↦ inner ℝ (gradient β x) (gradient ψ x)) := by
      obtain ⟨Cβ, hCβ⟩ := gradient_bound_of_locallyLipschitz
        (hβ_cd.of_le (by simp)).locallyLipschitz hcψ
      obtain ⟨Cg, hCg⟩ := gradient_bound_of_locallyLipschitz hψ_lip hcψ
      have hig_on : IntegrableOn (fun x ↦ inner ℝ (gradient β x) (gradient ψ x)) (tsupport ψ) := by
        apply (continuousOn_const.integrableOn_compact hcψ
          (f := fun _ : Space (m + 1) ↦ (Cβ : ℝ) * (Cg : ℝ))).mono'
          ((measurable_gradient β).inner (𝕜 := ℝ) (measurable_gradient ψ)).aestronglyMeasurable
        filter_upwards [ae_restrict_mem (isClosed_tsupport ψ).measurableSet] with x hx
        exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hCβ x hx) (hCg x hx) (norm_nonneg _) Cβ.coe_nonneg)
      exact hig_on.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
        simp [gradient, fderiv_of_notMem_tsupport ℝ hx])
    have his_V : Integrable (fun x ↦ f (V x) * ψ x) :=
      (hfV_cont.mul hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
    have his_Vt : Integrable (fun x ↦ f (V_tilde x) * ψ x) :=
      (hfVt_cont.mul hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
    have hi_Mdiff : Integrable (fun x ↦ M * (V_tilde x - V x) * ψ x) :=
      ((continuous_const.mul (hVt.continuous.sub hV.continuous)).mul
        hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
    have hi_Mβ : Integrable (fun x ↦ M * β x * ψ x) :=
      ((continuous_const.mul hβ_cd.continuous).mul
        hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
    have hi_Mδ : Integrable (fun x ↦ M * δ * ψ x) :=
      (continuous_const.mul hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
    rw [integral_sub hig_V his_V] at htest_V
    rw [integral_sub hig_Vt his_Vt] at htest_Vt
    have hreac_nn : 0 ≤ (∫ x, f (V_tilde x) * ψ x) - (∫ x, f (V x) * ψ x) +
        ∫ x, M * (V_tilde x - V x) * ψ x := by
      have hsub1 := integral_sub his_Vt his_V
      have hadd1 := integral_add (his_Vt.sub his_V) hi_Mdiff
      dsimp only [Pi.sub_apply] at hadd1
      rw [← hsub1, ← hadd1]
      apply integral_nonneg
      intro x
      dsimp only [Pi.zero_apply]
      have hd_f := hLf.dist_le_mul (V_tilde x) (hVt_val x) (V x) (hV_val x)
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (horder x))] at hd_f
      have h1 : -(Lf : ℝ) * (V_tilde x - V x) ≤ f (V_tilde x) - f (V x) := by
        have hle := neg_abs_le (f (V_tilde x) - f (V x))
        linarith
      have h2 : 0 ≤ (f (V_tilde x) - f (V x) + M * (V_tilde x - V x)) * ψ x := by
        apply mul_nonneg _ (le_max_right _ _)
        dsimp only [M]
        nlinarith [horder x]
      linarith
    have hδ_nn : 0 ≤ ∫ x, M * δ * ψ x :=
      integral_nonneg (fun _ ↦ mul_nonneg (mul_nonneg hM_pos.le hδ.le) (le_max_right _ _))
    -- Almost everywhere on `Space (m + 1)`, `⟨∇w, ∇ψ⟩ = -‖∇ψ‖² ≤ 0` and `M * w * ψ = -M * ψ²`
    have hae_ψ : ∀ᵐ x, DifferentiableAt ℝ ψ x := by
      have he (n : ℕ) : ∀ᵐ x, x ∈ closedBall (0 : Space (m + 1)) (n + 1) →
          DifferentiableWithinAt ℝ ψ (closedBall 0 (n + 1)) x := by
        obtain ⟨L, hL⟩ := hψ_lip.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
          (isCompact_closedBall 0 (n + 1))
        exact hL.ae_differentiableWithinAt_of_mem
      filter_upwards [ae_all_iff.mpr he] with x hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      have hb : x ∈ ball (0 : Space (m + 1)) (n + 1) := by
        simp only [mem_ball, dist_zero_right]; linarith
      exact (hx n (ball_subset_closedBall hb)).differentiableAt (closedBall_mem_nhds_of_mem hb)
    have hgrad_split : (∫ x, inner ℝ (gradient V_tilde x) (gradient ψ x)) -
        (∫ x, inner ℝ (gradient V x) (gradient ψ x)) -
        (∫ x, inner ℝ (gradient β x) (gradient ψ x)) ≤ 0 := by
      have hsub1 := integral_sub hig_Vt hig_V
      have hsub2 := integral_sub (hig_Vt.sub hig_V) hig_β
      dsimp only [Pi.sub_apply] at hsub2
      rw [← hsub1, ← hsub2]
      apply integral_nonpos_of_ae
      filter_upwards [ae_differentiableAt_lipschitz hV,
        ae_differentiableAt_lipschitz hVt, hae_ψ] with x hdV hdVt hdψ
      dsimp only [Pi.zero_apply]
      have hdβ : DifferentiableAt ℝ β x :=
        (hβ_cd2.of_le (by norm_num)).differentiable one_ne_zero x
      have hdw : DifferentiableAt ℝ w x :=
        ((hdVt.sub hdV).sub hdβ).add (differentiableAt_const δ)
      have hgw : gradient w x = gradient V_tilde x - gradient V x - gradient β x := by
        have hfw : HasFDerivAt w (fderiv ℝ V_tilde x - fderiv ℝ V x - fderiv ℝ β x) x :=
          ((hdVt.hasFDerivAt.sub hdV.hasFDerivAt).sub hdβ.hasFDerivAt).add_const δ
        simp only [gradient, hfw.fderiv, map_sub]
      have hlin : inner ℝ (gradient V_tilde x) (gradient ψ x) -
          inner ℝ (gradient V x) (gradient ψ x) -
          inner ℝ (gradient β x) (gradient ψ x) =
          inner ℝ (gradient w x) (gradient ψ x) := by
        rw [hgw, inner_sub_left, inner_sub_left]
      rw [hlin]
      by_cases hneg : w x < 0
      · have hev : ψ =ᶠ[𝓝 x] fun y ↦ -w y := by
          filter_upwards [(isOpen_lt hw_lip.continuous continuous_const).mem_nhds hneg] with y hy
          exact max_eq_left (neg_nonneg.mpr hy.le)
        have hgψ : gradient ψ x = -gradient w x := by
          rw [hev.gradient_eq]
          simp [gradient]
        rw [hgψ, inner_neg_right, real_inner_self_eq_norm_sq]
        exact neg_nonpos.mpr (sq_nonneg _)
      · push Not at hneg
        have hψ0 : ψ x = 0 := max_eq_right (neg_nonpos.mpr hneg)
        have hmin_ψ : IsLocalMin ψ x := by
          filter_upwards with y
          rw [hψ0]
          exact le_max_right _ _
        have hgψ : gradient ψ x = 0 := by
          simp [gradient, hmin_ψ.fderiv_eq_zero]
        rw [hgψ, inner_zero_right]
    have hmass_eq : (∫ x, M * (V_tilde x - V x) * ψ x) - (∫ x, M * β x * ψ x) +
        (∫ x, M * δ * ψ x) = -(M * ∫ x, ψ x ^ 2) := by
      have hsub1 := integral_sub hi_Mdiff hi_Mβ
      have hadd1 := integral_add (hi_Mdiff.sub hi_Mβ) hi_Mδ
      dsimp only [Pi.sub_apply] at hadd1
      rw [← hsub1, ← hadd1, ← integral_const_mul, ← integral_neg]
      apply integral_congr_ae
      refine Eventually.of_forall (fun x ↦ ?_)
      dsimp only [Pi.neg_apply]
      have h1 : M * (V_tilde x - V x) * ψ x - M * β x * ψ x + M * δ * ψ x =
          M * w x * ψ x := by dsimp only [w]; ring
      rw [h1]
      by_cases hneg : w x < 0
      · dsimp only [ψ]
        rw [max_eq_left (neg_nonneg.mpr hneg.le)]
        ring
      · push Not at hneg
        dsimp only [ψ]
        rw [max_eq_right (neg_nonpos.mpr hneg)]
        ring
    have hψ_sq_le : M * (∫ x, ψ x ^ 2) ≤ 0 := by
      linarith [htest_V, htest_Vt, hβ_sub_int, hreac_nn, hδ_nn, hgrad_split, hmass_eq]
    have hψ_x₀_pos : 0 < ψ x₀ := by
      dsimp only [ψ, w, β, δ]
      apply lt_max_of_lt_left
      linarith
    have hψ_sq_cont : Continuous (fun x ↦ ψ x ^ 2) := hψ_lip.continuous.pow 2
    have hcψ_sq : HasCompactSupport (fun x ↦ ψ x ^ 2) :=
      hcψ.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_comp_subset (g := fun t : ℝ ↦ t ^ 2) (by simp) ψ)
    have hψ_sq_pos : 0 < ∫ x, ψ x ^ 2 :=
      integral_pos_of_integrable_nonneg_nonzero hψ_sq_cont
        (hψ_sq_cont.integrable_of_hasCompactSupport hcψ_sq)
        (fun _ ↦ sq_nonneg _) (pow_ne_zero 2 hψ_x₀_pos.ne')
    exact (not_lt_of_ge hψ_sq_le) (mul_pos hM_pos hψ_sq_pos)
  -- Step 4: Evaluate along `s • ν` (`0 < s < r / 2`) and divide by `s → 0⁺` for contradiction
  let b_star : ℝ := 2 * ε * α * r * Real.exp (-α * r ^ 2)
  have hb_star_pos : 0 < b_star := by
    dsimp only [b_star]
    exact mul_pos (mul_pos (mul_pos (mul_pos two_pos hε_pos) hα) hr_pos) (Real.exp_pos _)
  have hderiv_bar : HasDerivAt
      (fun s : ℝ ↦ ε * (Real.exp (-α * (r - s) ^ 2) - Real.exp (-α * r ^ 2))) b_star 0 := by
    have hd_sub : HasDerivAt (fun s : ℝ ↦ r - s) (-1) 0 :=
      ((hasDerivAt_const (0 : ℝ) r).sub (hasDerivAt_id 0)).congr_deriv (by ring)
    have hd_sq : HasDerivAt (fun s : ℝ ↦ (r - s) ^ 2) (2 * r * (-1)) 0 :=
      ((hasDerivAt_pow 2 (r - 0)).comp (0 : ℝ) hd_sub).congr_deriv (by ring)
    have hd_exp : HasDerivAt (fun s : ℝ ↦ Real.exp (-α * (r - s) ^ 2))
        (Real.exp (-α * (r - 0) ^ 2) * (-α * (2 * r * (-1)))) 0 :=
      (hd_sq.const_mul (-α)).exp
    exact ((hd_exp.sub_const (Real.exp (-α * r ^ 2))).const_mul ε).congr_deriv (by
      rw [sub_zero]; dsimp only [b_star]; ring)
  have ht_low : Tendsto
      (fun s : ℝ ↦ ε * (Real.exp (-α * (r - s) ^ 2) - Real.exp (-α * r ^ 2)) / s)
      (𝓝[>] 0) (𝓝 b_star) := by
    have hd_slope := hderiv_bar.tendsto_slope_zero_right
    simpa only [zero_add, sub_self, mul_zero, sub_zero, smul_eq_mul, div_eq_inv_mul] using hd_slope
  have ht_up : Tendsto (fun s : ℝ ↦ κ - V (s • ν) / s) (𝓝[>] 0) (𝓝 0) := by
    have hsub := (tendsto_const_nhds (x := κ)).sub hslope_V
    rwa [sub_self] at hsub
  have hev_ord : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ε * (Real.exp (-α * (r - s) ^ 2) - Real.exp (-α * r ^ 2)) / s ≤ κ - V (s • ν) / s := by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hr_pos)] with s hs
    have hs_pos : 0 < s := hs.1
    have hs_lt : s < r := hs.2.trans (half_lt_self hr_pos)
    have hnorm_sc : ‖s • ν - c_in‖ = r - s := by
      have heq : s • ν - c_in = -(r - s) • ν := by dsimp only [c_in]; module
      rw [heq, norm_smul, hν, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos (sub_pos.mpr hs_lt)]
    have hmem_b : s • ν ∈ ball c_in r := by
      rw [mem_ball, dist_eq_norm, hnorm_sc]
      linarith
    have hbar_le := hann_le (s • ν) hmem_b
    dsimp only [annularBarrier, radialGaussian] at hbar_le
    rw [hnorm_sc] at hbar_le
    have hVt_le : V_tilde (s • ν) ≤ κ * s := by
      have hd := hVt.dist_le_mul (s • ν) 0
      rw [hVt0, Real.dist_eq, sub_zero, dist_zero_right, norm_smul, hν, mul_one,
        Real.norm_of_nonneg hs_pos.le] at hd
      exact (le_abs_self _).trans hd
    have hsub_vt : V_tilde (s • ν) - V (s • ν) ≤ κ * s - V (s • ν) := by linarith
    have hdiv := div_le_div_of_nonneg_right (hbar_le.trans hsub_vt) hs_pos.le
    have hrew : (κ * s - V (s • ν)) / s = κ - V (s • ν) / s := by
      rw [sub_div, mul_div_cancel_right₀ κ hs_pos.ne']
    exact hdiv.trans_eq hrew
  have hle_zero : b_star ≤ 0 := le_of_tendsto_of_tendsto ht_low ht_up hev_ord
  linarith

end SerrinEpigraph
