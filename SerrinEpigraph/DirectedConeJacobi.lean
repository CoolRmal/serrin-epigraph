module

public import SerrinEpigraph.BoundaryChartGluing
public import SerrinEpigraph.SingularCutoff

/-!
# Directed minimizing cones: `|A|² ⟪ν, eₙ⟫ = 0` at regular boundary points

Steps A–C of the alternative splitting argument (blueprint `docs/rigidity-proof/one-sided.md`,
§5A). Let `E` be a directed minimizing cone in `Space (m + 1)` whose singular set is
`μH[s]`-null for `s > m + 1 - 8`, and assume `C1RegularSmoothHyp`. At every boundary point `x₀` of
a smooth chart `(U, F)` of `E`,
`|A|²(x₀) ⟪ν(x₀), eₙ⟫ = 0` (`IsDirectedMinimizingCone.sqNorm_mul_inner_vertical_eq_zero`).

Proof. The vertical component `w = ⟪ν, eₙ⟫` is nonnegative by vertical monotonicity. Suppose
`|A|² w ≥ c > 0` near `x₀`. Let `ψ` be a radial cutoff equal to one near `x₀` and `ηₖ` the capacity
cutoffs of the singular set (step A, `SingularCutoff`), with `∫ |Dηₖ|² dμ → 0`, `μ` the perimeter
measure. The function `θ = ψ ηₖ` is supported away from the singular set; gluing charts gives a
single chart containing the regular part of its support, and a smooth Urysohn factor makes `θ`
supported in the chart without changing it near the boundary. On this chart:
* stability (`IsSmoothBoundaryChart.stability_inequality`) gives
  `Q = ∫ θ² |A|² ≤ ∫ |δθ|² ≤ 2 ∫ |Dηₖ|² + 2 ∫ |Dψ|²` (step B);
* the weak Jacobi equation with test function `θ²` gives
  `∫ θ² |A|² w = ∫ ⟪δ θ², δ w⟫`; on a cone `⟪δψ, δw⟫ = 0` because `ψ` is radial and
  `⟪δ w, x⟫ = 0`, so the right side is at most `t ∫ |Dηₖ|² + t⁻¹ Q` for every `t > 0` (step C).
Letting `k → ∞` and then `t → ∞` contradicts `∫ θ² |A|² w ≥ (c / 2) μ(B(x₀, r)) > 0`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff ENNReal

namespace SerrinEpigraph

/-! ### 1. Pointwise estimates -/

/-- The radial cutoff `1 - doubledBallCutoff 0 R` has radial gradient. -/
theorem fderiv_one_sub_doubledBallCutoff_apply_eq_zero {d : ℕ} (R : ℝ) {z w : Space d}
    (hzw : inner ℝ z w = 0) :
    fderiv ℝ (fun x ↦ 1 - doubledBallCutoff (0 : Space d) R x) z w = 0 := by
  rw [((hasFDerivAt_doubledBallCutoff (0 : Space d) R z).const_sub 1).fderiv,
    (hasFDerivAt_doubledBallProfile (0 : Space d) R z).fderiv]
  simp [hzw]

/-- Pointwise bound for the stability integrand of a product `θ = ψ η` of cutoffs. -/
theorem norm_sq_tangentialGradient_le_of_eventuallyEq_mul {d : ℕ} {F ψ η θ : Space d → ℝ}
    {y : Space d} (hy : gradient F y ≠ 0) (hψ : DifferentiableAt ℝ ψ y)
    (hη : DifferentiableAt ℝ η y) (hψ1 : |ψ y| ≤ 1) (hη1 : |η y| ≤ 1)
    (hθ : θ =ᶠ[𝓝 y] fun x ↦ ψ x * η x) :
    ‖tangentialGradient F θ y‖ ^ 2 ≤ 2 * ‖fderiv ℝ η y‖ ^ 2 + 2 * ‖fderiv ℝ ψ y‖ ^ 2 := by
  have hdθ : HasFDerivAt θ (ψ y • fderiv ℝ η y + η y • fderiv ℝ ψ y) y :=
    (hψ.hasFDerivAt.fun_mul hη.hasFDerivAt).congr_of_eventuallyEq hθ
  have h1 := norm_tangentialGradient_le_norm_fderiv (f := θ) hy
  rw [hdθ.fderiv] at h1
  have h2 : ‖ψ y • fderiv ℝ η y + η y • fderiv ℝ ψ y‖ ≤ ‖fderiv ℝ η y‖ + ‖fderiv ℝ ψ y‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hψ1
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hη1
  have h3 : ‖tangentialGradient F θ y‖ ^ 2 ≤ (‖fderiv ℝ η y‖ + ‖fderiv ℝ ψ y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
  nlinarith [sq_nonneg (‖fderiv ℝ η y‖ - ‖fderiv ℝ ψ y‖)]

private theorem two_mul_le_add_aux {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    2 * a * b ≤ t * a ^ 2 + t⁻¹ * b ^ 2 := by
  have hkey : t * a ^ 2 + t⁻¹ * b ^ 2 - 2 * a * b = t⁻¹ * (t * a - b) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ t⁻¹ * (t * a - b) ^ 2 := mul_nonneg (inv_nonneg.mpr ht.le) (sq_nonneg _)
  linarith

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

/-- Pointwise bound for the Jacobi integrand `⟪δ θ², δ ⟪ν, e⟫⟫` on a cone, for `θ = ψ η` with a
radial `ψ`: it is at most `t |Dη|² + t⁻¹ θ² |A|²`. -/
theorem abs_inner_tangentialGradient_mul_self_le (h : IsSmoothBoundaryChart E U F)
    (hcone : ∀ x ∈ measureTheoreticBoundary E, ∀ a : ℝ, 0 < a →
      a • x ∈ measureTheoreticBoundary E)
    (hy : y ∈ U) (hFy : F y = 0) {ψ η θ : Space d → ℝ} (hψ : DifferentiableAt ℝ ψ y)
    (hη : DifferentiableAt ℝ η y) (hψ1 : |ψ y| ≤ 1) (hθ : θ =ᶠ[𝓝 y] fun x ↦ ψ x * η x)
    (hrad : ∀ w, inner ℝ y w = 0 → fderiv ℝ ψ y w = 0) {e : Space d} (he : ‖e‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    |inner ℝ (tangentialGradient F (fun x ↦ θ x * θ x) y)
        (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) e) y)| ≤
      t * ‖fderiv ℝ η y‖ ^ 2 + t⁻¹ * (θ y ^ 2 * sqNormSecondFundamentalForm F y) := by
  set W := tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) e) y with hW
  have hWy : inner ℝ y W = 0 := by
    rw [real_inner_comm]
    exact h.inner_tangentialGradient_inner_chartNormal_self hcone hy hFy e
  have hW2 : ‖W‖ ^ 2 ≤ sqNormSecondFundamentalForm F y := by
    have h1 := h.norm_sq_tangentialGradient_inner_chartNormal_le hy e
    rwa [he, one_pow, mul_one] at h1
  have hθy : θ y = ψ y * η y := hθ.eq_of_nhds
  have hdθ : HasFDerivAt θ (ψ y • fderiv ℝ η y + η y • fderiv ℝ ψ y) y :=
    (hψ.hasFDerivAt.fun_mul hη.hasFDerivAt).congr_of_eventuallyEq hθ
  have hdθθ := hdθ.fun_mul hdθ
  rw [h.inner_tangentialGradient_tangentialGradient_eq_fderiv hy, hdθθ.fderiv]
  have hval : (θ y • (ψ y • fderiv ℝ η y + η y • fderiv ℝ ψ y) +
      θ y • (ψ y • fderiv ℝ η y + η y • fderiv ℝ ψ y)) W =
      2 * (θ y * (ψ y * fderiv ℝ η y W)) := by
    simp only [add_apply, smul_apply, smul_eq_mul, hrad W hWy, mul_zero, add_zero]
    ring
  rw [hval]
  have h1 : |fderiv ℝ η y W| ≤ ‖fderiv ℝ η y‖ * ‖W‖ := by
    rw [← Real.norm_eq_abs]
    exact (fderiv ℝ η y).le_opNorm W
  have hX : |2 * (θ y * (ψ y * fderiv ℝ η y W))| ≤
      2 * (|ψ y| * ‖fderiv ℝ η y‖) * (|θ y| * ‖W‖) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    calc 2 * (|θ y| * (|ψ y| * |fderiv ℝ η y W|))
        ≤ 2 * (|θ y| * (|ψ y| * (‖fderiv ℝ η y‖ * ‖W‖))) := by gcongr
      _ = 2 * (|ψ y| * ‖fderiv ℝ η y‖) * (|θ y| * ‖W‖) := by ring
  have ha2 : (|ψ y| * ‖fderiv ℝ η y‖) ^ 2 ≤ ‖fderiv ℝ η y‖ ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (abs_nonneg _) hψ1)
  have hb2 : (|θ y| * ‖W‖) ^ 2 ≤ θ y ^ 2 * sqNormSecondFundamentalForm F y := by
    rw [mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
  calc |2 * (θ y * (ψ y * fderiv ℝ η y W))|
      ≤ 2 * (|ψ y| * ‖fderiv ℝ η y‖) * (|θ y| * ‖W‖) := hX
    _ ≤ t * (|ψ y| * ‖fderiv ℝ η y‖) ^ 2 + t⁻¹ * (|θ y| * ‖W‖) ^ 2 := two_mul_le_add_aux ht _ _
    _ ≤ t * ‖fderiv ℝ η y‖ ^ 2 + t⁻¹ * (θ y ^ 2 * sqNormSecondFundamentalForm F y) := by
        gcongr

end IsSmoothBoundaryChart

/-- A function continuous on an open set and vanishing off a compact subset of it is integrable
for every locally finite measure. -/
private theorem integrable_of_continuousOn_of_eq_zero_aux {d : ℕ} {μ : Measure (Space d)}
    [IsFiniteMeasureOnCompacts μ] {U K : Set (Space d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : Space d → ℝ} (hf : ContinuousOn f U) (h0 : ∀ x, x ∉ K → f x = 0) :
    Integrable f μ := by
  refine (continuous_of_continuousOn_of_eq_zero hU hK.isClosed hKU hf h0).integrable_of_hasCompactSupport ?_
  refine hK.of_isClosed_subset (isClosed_tsupport f) (closure_minimal (fun x hx ↦ ?_) hK.isClosed)
  by_contra hxK
  exact hx (h0 x hxK)

/-! ### 2. Steps A–C -/

/-- **Steps A–C.** For a directed minimizing cone with small singular set, the quantity
`|A|² ⟪ν, eₙ⟫` vanishes at every boundary point of every smooth chart. -/
theorem IsDirectedMinimizingCone.sqNorm_mul_inner_vertical_eq_zero {m : ℕ} (hm : 3 ≤ m)
    {E : Set (Space (m + 1))} (hE : IsDirectedMinimizingCone E) (hsmooth : C1RegularSmoothHyp)
    (hSnull : ∀ s : ℝ, ((m + 1 : ℕ) : ℝ) - 8 < s → μH[s] (singularSet E) = 0)
    {U : Set (Space (m + 1))} {F : Space (m + 1) → ℝ} (hU : IsSmoothBoundaryChart E U F)
    {x₀ : Space (m + 1)} (hx₀ : x₀ ∈ U) (hFx₀ : F x₀ = 0) :
    sqNormSecondFundamentalForm F x₀ * inner ℝ (chartNormal F x₀) (verticalDirection m) = 0 := by
  classical
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  set e := verticalDirection m with he
  have he1 : ‖e‖ = 1 := by simp [he, verticalDirection]
  have hmin := hE.minimizer
  have hmeas := hE.measurableSet
  have hcone : ∀ x ∈ measureTheoreticBoundary E, ∀ a : ℝ, 0 < a →
      a • x ∈ measureTheoreticBoundary E :=
    fun x hx a ha ↦ (hE.isMinimizingCone.smul_mem_measureTheoreticBoundary_iff ha x).mpr hx
  set g₀ : Space (m + 1) → ℝ :=
    fun z ↦ sqNormSecondFundamentalForm F z * inner ℝ (chartNormal F z) e with hg₀
  have hg₀nn : 0 ≤ g₀ x₀ := mul_nonneg (sqNormSecondFundamentalForm_nonneg F x₀)
    (hU.inner_chartNormal_nonneg_of_monotone hE.vertical hx₀ hFx₀)
  by_contra hne
  have hc : 0 < g₀ x₀ := lt_of_le_of_ne hg₀nn (Ne.symm hne)
  set c := g₀ x₀ with hcdef
  -- distance to the singular set
  have hx₀S : x₀ ∉ singularSet E := fun h ↦ h.2 (hU.isC1BoundaryPoint hx₀ hFx₀)
  have hx₀B : x₀ ∈ measureTheoreticBoundary E := hU.mem_measureTheoreticBoundary hx₀ hFx₀
  obtain ⟨ε₀, hε₀, hε₀S⟩ :=
    Metric.isOpen_iff.mp (isClosed_singularSet E).isOpen_compl x₀ hx₀S
  -- a ball around `x₀` on which `g₀ > c / 2`
  have hg₀cont : ContinuousOn g₀ U :=
    hU.continuousOn_sqNormSecondFundamentalForm.mul
      (hU.contDiffOn_chartNormal.continuousOn.inner continuousOn_const)
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.eventually_nhds_iff_ball.mp
    (((hg₀cont.continuousAt (hU.isOpen.mem_nhds hx₀)).eventually
      (lt_mem_nhds (half_lt_self hc))).and (hU.isOpen.mem_nhds hx₀))
  set r := min r₁ (min (ε₀ / 2) 1) with hr
  have hr0 : 0 < r := lt_min hr₁ (lt_min (by positivity) one_pos)
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrε : r ≤ ε₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hballU : ball x₀ r ⊆ U := fun z hz ↦ (hr₁sub z (ball_subset_ball hrr₁ hz)).2
  have hballg : ∀ z ∈ ball x₀ r, c / 2 < g₀ z := fun z hz ↦
    (hr₁sub z (ball_subset_ball hrr₁ hz)).1
  -- the perimeter measure
  obtain ⟨μ, hμloc, -, hμ⟩ := exists_global_perimeter_measure b hmeas
    (fun n ↦ hmin.perimeter_ball_ne_top 0 _ (by positivity) (subset_univ _))
  have := hμloc
  have hμ' : ∀ V, IsOpen V → V ⊆ univ → μ V = variationalPerimeter b E V := fun V hV _ ↦ hμ V hV
  have hμB : μ (univ \ measureTheoreticBoundary E) = 0 := hmin.measure_sdiff_boundary_eq_zero μ hμ'
  have hμball : 0 < μ.real (ball x₀ r) := by
    have h1 : 0 < variationalPerimeter b E (ball x₀ r) :=
      (hmin.variationalPerimeter_ball_pos_iff (subset_univ _)).mpr ⟨x₀, mem_ball_self hr0, hx₀B⟩
    rw [measureReal_def, hμ _ isOpen_ball]
    exact ENNReal.toReal_pos h1.ne' (hmin.perimeter_ball_ne_top x₀ r hr0 (subset_univ _))
  -- the radial cutoff `ψ`
  set R : ℝ := ‖x₀‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  set ψ : Space (m + 1) → ℝ := fun z ↦ 1 - doubledBallCutoff (0 : Space (m + 1)) R z with hψ
  have hψs : ContDiff ℝ ∞ ψ := contDiff_const.sub (contDiff_doubledBallCutoff 0 R)
  have hψ1 : ∀ z, |ψ z| ≤ 1 := fun z ↦ by
    have h1 := doubledBallCutoff_nonneg (0 : Space (m + 1)) R z
    have h2 := doubledBallCutoff_le_one (0 : Space (m + 1)) R z
    rw [abs_le]
    constructor <;> simp only [hψ] <;> linarith
  have hψ_one : ∀ z, ‖z‖ ≤ R → ψ z = 1 := fun z hz ↦ by
    simp only [hψ]
    rw [doubledBallCutoff_eq_zero hR0 (by rwa [sub_zero])]
    ring
  have hψ_zero : ∀ z, 2 * R ≤ ‖z‖ → ψ z = 0 := fun z hz ↦ by
    simp only [hψ]
    rw [doubledBallCutoff_eq_one hR0 (by rwa [sub_zero])]
    ring
  have hψsupp : tsupport ψ ⊆ closedBall 0 (2 * R) := by
    refine closure_minimal (fun z hz ↦ ?_) isClosed_closedBall
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    exact hz (hψ_zero z (not_le.mp hlt).le)
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall 0 (2 * R)).of_isClosed_subset (isClosed_tsupport _) hψsupp
  have hψrad : ∀ z w, inner ℝ z w = 0 → fderiv ℝ ψ z w = 0 := fun z w hzw ↦
    fderiv_one_sub_doubledBallCutoff_apply_eq_zero R hzw
  have hψDc : HasCompactSupport (fun x ↦ ‖fderiv ℝ ψ x‖ ^ 2) := by
    refine hψc.mono' fun x hx ↦ ?_
    by_contra hxs
    exact hx (by show ‖fderiv ℝ ψ x‖ ^ 2 = 0; rw [fderiv_of_notMem_tsupport ℝ hxs, norm_zero]; ring)
  have hψDcont : Continuous (fun x ↦ ‖fderiv ℝ ψ x‖ ^ 2) :=
    (hψs.continuous_fderiv (by simp)).norm.pow 2
  have hψint : Integrable (fun x ↦ ‖fderiv ℝ ψ x‖ ^ 2) μ :=
    hψDcont.integrable_of_hasCompactSupport hψDc
  set M := ∫ x, ‖fderiv ℝ ψ x‖ ^ 2 ∂μ with hMdef
  have hM : 0 ≤ M := integral_nonneg fun x ↦ sq_nonneg _
  have hψball : ∀ z ∈ ball x₀ r, ψ z = 1 := by
    intro z hz
    apply hψ_one
    have h1 : ‖z‖ ≤ ‖x₀‖ + ‖z - x₀‖ := by simpa using norm_add_le x₀ (z - x₀)
    have h2 : ‖z - x₀‖ < r := by rw [← dist_eq_norm]; exact mem_ball.mp hz
    linarith
  -- step A: the capacity cutoffs of the singular set
  set ρ₀ : ℝ := 2 * R + 1 with hρ₀
  set Sc := singularSet E ∩ closedBall (0 : Space (m + 1)) ρ₀ with hScdef
  have hSc : IsCompact Sc := (isCompact_closedBall _ _).inter_left (isClosed_singularSet E)
  have hScnull : μH[(m : ℝ) - 2] Sc = 0 :=
    measure_mono_null inter_subset_left (hSnull _ (by push_cast; linarith))
  have hgrowth : ∀ x ∈ Sc, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (closedBall x ρ) ≤ ENNReal.ofReal (minimizerPerimeterUpperConst m * ρ ^ (m : ℝ)) := by
    intro x _ ρ hρ _
    rw [Real.rpow_natCast]
    exact hmin.measure_closedBall_le μ hμ' hρ (subset_univ _)
  obtain ⟨η, hηs, hη01, hηV, -, hηone, -, hηint, hηlim, -, -⟩ :=
    exists_smooth_cutoff_seq_of_hausdorffMeasure_eq_zero μ (A := minimizerPerimeterUpperConst m)
      (r₀ := 1) (k := (m : ℝ)) (by exact_mod_cast (by omega : 2 < m)) one_pos hgrowth hSc
      hScnull
  have hη1 : ∀ k x, |η k x| ≤ 1 := fun k x ↦
    abs_le.mpr ⟨by linarith [(hη01 k x).1], (hη01 k x).2⟩
  obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt (show 0 < ε₀ / 2 by positivity)
  have hηball : ∀ k ≥ k₀, ∀ z ∈ ball x₀ r, η k z = 1 := by
    intro k hk z hz
    apply hηone k z
    intro hzt
    obtain ⟨s, hsSc, hzs⟩ := mem_thickening_iff.mp hzt
    have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    have hxs : dist s x₀ < ε₀ := by
      calc dist s x₀ ≤ dist s z + dist z x₀ := dist_triangle _ _ _
        _ < ε₀ / 2 + ε₀ / 2 := by
          refine add_lt_add ?_ (lt_of_lt_of_le (mem_ball.mp hz) hrε)
          rw [dist_comm]
          linarith
        _ = ε₀ := by ring
    exact hε₀S (mem_ball.mpr hxs) hsSc.1
  -- the key estimate for every large `k`
  have hkey : ∀ k ≥ k₀, ∀ t : ℝ, 0 < t →
      c / 2 * μ.real (ball x₀ r) ≤
        t * ∫ x, ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ +
          t⁻¹ * (2 * ∫ x, ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ + 2 * M) := by
    intro k hk t ht
    have hηk : ContDiff ℝ ∞ (η k) := hηs k
    obtain ⟨V, hVopen, hScV, hηV0⟩ := hηV k
    set θ₀ : Space (m + 1) → ℝ := fun z ↦ ψ z * η k z with hθ₀
    have hθ₀s : ContDiff ℝ ∞ θ₀ := hψs.mul hηk
    have hθ₀c : HasCompactSupport θ₀ := hψc.mul_right
    have hθ₀supp : tsupport θ₀ ⊆ closedBall 0 (2 * R) := tsupport_mul_subset_left.trans hψsupp
    have hηsupp : tsupport (η k) ⊆ Vᶜ :=
      closure_minimal (fun z hz hzV ↦ hz (hηV0 z hzV)) hVopen.isClosed_compl
    have hθ₀supp' : tsupport θ₀ ⊆ Vᶜ := tsupport_mul_subset_right.trans hηsupp
    -- the regular part of the support lies in one chart
    set K := tsupport θ₀ ∩ measureTheoreticBoundary E with hK
    have hKc : IsCompact K := hθ₀c.inter_right (isClosed_measureTheoreticBoundary E)
    have hKS : Disjoint K (singularSet E) := by
      rw [disjoint_left]
      intro z hzK hzS
      have hz1 : z ∈ closedBall (0 : Space (m + 1)) ρ₀ :=
        closedBall_subset_closedBall (by linarith) (hθ₀supp hzK.1)
      exact hθ₀supp' hzK.1 (hScV ⟨hzS, hz1⟩)
    obtain ⟨U₁, F₁, hKU₁, h₁⟩ := hsmooth.exists_chart_superset hmin hKc inter_subset_right hKS
    set Ω : Set (Space (m + 1)) := ball 0 ρ₀ with hΩ
    set U' := U₁ ∩ Ω with hU'
    have h' : IsSmoothBoundaryChart E U' F₁ :=
      h₁.mono (h₁.isOpen.inter isOpen_ball) inter_subset_left
    have hU'Ω : U' ⊆ Ω := inter_subset_right
    have hKU' : K ⊆ U' := fun z hz ↦
      ⟨hKU₁ hz, closedBall_subset_ball (by linarith) (hθ₀supp hz.1)⟩
    -- a smooth Urysohn factor puts the support inside the chart
    obtain ⟨χ, hχs, -, hχ1, hχU', hχc⟩ :=
      exists_contDiff_eventually_one_tsupport_subset hKc h'.isOpen hKU'
    set θ : Space (m + 1) → ℝ := fun z ↦ θ₀ z * χ z with hθ
    have hθs : ContDiff ℝ ∞ θ := hθ₀s.mul hχs
    have hθc : HasCompactSupport θ := hχc.mul_left
    have hθU' : tsupport θ ⊆ U' := tsupport_mul_subset_right.trans hχU'
    have hθeq : ∀ z ∈ measureTheoreticBoundary E, θ =ᶠ[𝓝 z] fun x ↦ ψ x * η k x := by
      intro z hzB
      by_cases hz : z ∈ tsupport θ₀
      · filter_upwards [hχ1 z ⟨hz, hzB⟩] with w hw
        simp only [hθ, hθ₀, hw, mul_one]
      · filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
        simp only [Pi.zero_apply, hθ₀] at hw
        simp only [hθ, hθ₀, hw, zero_mul]
    -- the perimeter measure on `Ω`
    obtain ⟨νΩ, hp⟩ := exists_isPerimeterPolarOn_of_perimeter_measure b hmeas isOpen_ball
      (hmin.perimeter_ball_ne_top 0 ρ₀ (by positivity) (subset_univ _)) μ hμ
    have hminΩ : IsPerimeterMinimizingIn b E Ω := hmin.isPerimeterMinimizingIn isOpen_ball
      (subset_univ _)
    have : IsFiniteMeasure (μ.restrict U') := IsSmoothBoundaryChart.isFiniteMeasure_restrict hp hU'Ω
    have hbd : ∀ᵐ x ∂μ.restrict U', x ∈ U' ∧ F₁ x = 0 :=
      (ae_restrict_mem h'.isOpen.measurableSet).and (h'.ae_restrict_eq_zero hp hU'Ω)
    -- step B: stability
    set Q := ∫ x in U', θ x ^ 2 * sqNormSecondFundamentalForm F₁ x ∂μ with hQdef
    have hstab := h'.stability_inequality hmeas hp hminΩ hU'Ω (hθs.of_le (by simp)) hθc hθU'
    have hS1 : ∫ x in U', ‖tangentialGradient F₁ θ x‖ ^ 2 ∂μ ≤
        ∫ x in U', (2 * ‖fderiv ℝ (η k) x‖ ^ 2 + 2 * ‖fderiv ℝ ψ x‖ ^ 2) ∂μ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun x ↦ sq_nonneg _)
        ((((hηint k).const_mul 2).add (hψint.const_mul 2)).restrict) ?_
      filter_upwards [hbd] with x hx
      exact norm_sq_tangentialGradient_le_of_eventuallyEq_mul (h'.gradient_ne_zero x hx.1)
        (hψs.differentiable (by simp) x) (hηk.differentiable (by simp) x) (hψ1 x) (hη1 k x)
        (hθeq x (h'.mem_measureTheoreticBoundary hx.1 hx.2))
    have hS2 : ∫ x in U', (2 * ‖fderiv ℝ (η k) x‖ ^ 2 + 2 * ‖fderiv ℝ ψ x‖ ^ 2) ∂μ ≤
        2 * ∫ x, ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ + 2 * M := by
      have h1 : ∫ x in U', ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ ≤ ∫ x, ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ :=
        setIntegral_le_integral (hηint k) (Eventually.of_forall fun x ↦ sq_nonneg _)
      have h2 : ∫ x in U', ‖fderiv ℝ ψ x‖ ^ 2 ∂μ ≤ M :=
        setIntegral_le_integral hψint (Eventually.of_forall fun x ↦ sq_nonneg _)
      rw [integral_add ((hηint k).const_mul 2).restrict (hψint.const_mul 2).restrict,
        integral_const_mul, integral_const_mul]
      linarith
    have hQ : Q ≤ 2 * ∫ x, ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ + 2 * M := hstab.trans (hS1.trans hS2)
    -- integrability of the curvature integrands
    have hθK : IsCompact (tsupport θ) := hθc
    have hQint : Integrable (fun x ↦ θ x ^ 2 * sqNormSecondFundamentalForm F₁ x) (μ.restrict U') :=
      (integrable_of_continuousOn_of_eq_zero_aux h'.isOpen hθK hθU'
        (f := fun x ↦ θ x ^ 2 * sqNormSecondFundamentalForm F₁ x)
        ((hθs.continuous.pow 2).continuousOn.mul h'.continuousOn_sqNormSecondFundamentalForm)
        (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx])).restrict
    have hRint : Integrable (fun x ↦ θ x * θ x * sqNormSecondFundamentalForm F₁ x *
        inner ℝ (chartNormal F₁ x) e) (μ.restrict U') :=
      (integrable_of_continuousOn_of_eq_zero_aux h'.isOpen hθK hθU'
        (f := fun x ↦ θ x * θ x * sqNormSecondFundamentalForm F₁ x *
          inner ℝ (chartNormal F₁ x) e)
        (((hθs.continuous.mul hθs.continuous).continuousOn.mul
          h'.continuousOn_sqNormSecondFundamentalForm).mul
          (h'.contDiffOn_chartNormal.continuousOn.inner continuousOn_const))
        (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx])).restrict
    -- step C: the weak Jacobi equation with test function `θ²`
    have hjac := h'.integral_inner_tangentialGradient_inner_chartNormal hmeas hp hminΩ hU'Ω
      (ζ := fun x ↦ θ x * θ x) ((hθs.mul hθs).of_le (by simp)) hθc.mul_left
      (tsupport_mul_subset_left.trans hθU') e
    have hJL : ∫ x in U', inner ℝ (tangentialGradient F₁ (fun x ↦ θ x * θ x) x)
        (tangentialGradient F₁ (fun x ↦ inner ℝ (chartNormal F₁ x) e) x) ∂μ ≤
        t * ∫ x, ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ + t⁻¹ * Q := by
      refine (le_abs_self _).trans (abs_integral_le_integral_abs.trans ?_)
      calc ∫ x in U', |inner ℝ (tangentialGradient F₁ (fun x ↦ θ x * θ x) x)
            (tangentialGradient F₁ (fun x ↦ inner ℝ (chartNormal F₁ x) e) x)| ∂μ
          ≤ ∫ x in U', (t * ‖fderiv ℝ (η k) x‖ ^ 2 +
              t⁻¹ * (θ x ^ 2 * sqNormSecondFundamentalForm F₁ x)) ∂μ := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun x ↦ abs_nonneg _)
              ((((hηint k).const_mul t).restrict).add (hQint.const_mul t⁻¹)) ?_
            filter_upwards [hbd] with x hx
            exact h'.abs_inner_tangentialGradient_mul_self_le hcone hx.1 hx.2
              (hψs.differentiable (by simp) x) (hηk.differentiable (by simp) x) (hψ1 x)
              (hθeq x (h'.mem_measureTheoreticBoundary hx.1 hx.2)) (hψrad x) he1 ht
        _ = t * ∫ x in U', ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ + t⁻¹ * Q := by
            rw [integral_add (((hηint k).const_mul t).restrict) (hQint.const_mul t⁻¹),
              integral_const_mul, integral_const_mul]
        _ ≤ t * ∫ x, ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ + t⁻¹ * Q :=
            add_le_add_left (mul_le_mul_of_nonneg_left (setIntegral_le_integral (hηint k)
              (Eventually.of_forall fun x ↦ sq_nonneg _)) ht.le) _
    -- the Jacobi integrand is at least `c / 2` near `x₀`
    have hball_sub : ball x₀ r ∩ measureTheoreticBoundary E ⊆ U' := by
      rintro z ⟨hz, hzB⟩
      refine hKU' ⟨subset_tsupport _ ?_, hzB⟩
      show ψ z * η k z ≠ 0
      rw [hψball z hz, hηball k hk z hz, mul_one]
      exact one_ne_zero
    have hμeq : μ.real (U' ∩ ball x₀ r) = μ.real (ball x₀ r) := by
      have hdiff : μ (ball x₀ r \ U') = 0 := by
        refine measure_mono_null (fun z hz ↦ ?_) hμB
        exact ⟨mem_univ z, fun hzB ↦ hz.2 (hball_sub ⟨hz.1, hzB⟩)⟩
      have h1 : μ (U' ∩ ball x₀ r) = μ (ball x₀ r) := by
        refine le_antisymm (measure_mono inter_subset_right) ?_
        calc μ (ball x₀ r) ≤ μ (ball x₀ r ∩ U') + μ (ball x₀ r \ U') :=
              measure_le_inter_add_sdiff μ _ _
          _ = μ (U' ∩ ball x₀ r) := by rw [hdiff, add_zero, inter_comm]
      rw [measureReal_def, measureReal_def, h1]
    have hJR : c / 2 * μ.real (ball x₀ r) ≤ ∫ x in U', θ x * θ x *
        sqNormSecondFundamentalForm F₁ x * inner ℝ (chartNormal F₁ x) e ∂μ := by
      have hfnn : 0 ≤ᵐ[μ.restrict U'] fun x ↦ θ x * θ x * sqNormSecondFundamentalForm F₁ x *
          inner ℝ (chartNormal F₁ x) e := by
        filter_upwards [hbd] with x hx
        exact mul_nonneg (mul_nonneg (mul_self_nonneg _) (sqNormSecondFundamentalForm_nonneg _ _))
          (h'.inner_chartNormal_nonneg_of_monotone hE.vertical hx.1 hx.2)
      have hbd' : ∀ᵐ x ∂μ.restrict (U' ∩ ball x₀ r), x ∈ U' ∩ ball x₀ r ∧ F₁ x = 0 :=
        (ae_restrict_mem (h'.isOpen.inter isOpen_ball).measurableSet).and
          (ae_restrict_of_ae_restrict_of_subset inter_subset_left (h'.ae_restrict_eq_zero hp hU'Ω))
      have : IsFiniteMeasure (μ.restrict (U' ∩ ball x₀ r)) :=
        IsSmoothBoundaryChart.isFiniteMeasure_restrict hp (inter_subset_left.trans hU'Ω)
      calc c / 2 * μ.real (ball x₀ r) = ∫ x in U' ∩ ball x₀ r, c / 2 ∂μ := by
            rw [setIntegral_const, smul_eq_mul, hμeq, mul_comm]
        _ ≤ ∫ x in U' ∩ ball x₀ r, θ x * θ x * sqNormSecondFundamentalForm F₁ x *
              inner ℝ (chartNormal F₁ x) e ∂μ := by
            refine integral_mono_ae (integrable_const _)
              (hRint.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) ?_
            filter_upwards [hbd'] with x hx
            have hxB : x ∈ measureTheoreticBoundary E :=
              h'.mem_measureTheoreticBoundary hx.1.1 hx.2
            have hxU : x ∈ U := hballU hx.1.2
            have hθx : θ x = 1 := by
              rw [(hθeq x hxB).eq_of_nhds, hψball x hx.1.2, hηball k hk x hx.1.2, mul_one]
            rw [hθx, one_mul, one_mul,
              hU.sqNormSecondFundamentalForm_eq_of_mem_boundary h' hxU hx.1.1 hxB,
              hU.chartNormal_eq_of_mem_boundary h' hxU hx.1.1 hxB]
            exact (hballg x hx.1.2).le
        _ ≤ ∫ x in U', θ x * θ x * sqNormSecondFundamentalForm F₁ x *
              inner ℝ (chartNormal F₁ x) e ∂μ :=
            setIntegral_mono_set hRint hfnn inter_subset_left.eventuallyLE
    have hQ' : t⁻¹ * Q ≤ t⁻¹ * (2 * ∫ x, ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ + 2 * M) :=
      mul_le_mul_of_nonneg_left hQ (inv_nonneg.mpr ht.le)
    have hjac' : ∫ x in U', inner ℝ (tangentialGradient F₁ (fun x ↦ θ x * θ x) x)
        (tangentialGradient F₁ (fun x ↦ inner ℝ (chartNormal F₁ x) e) x) ∂μ =
        ∫ x in U', θ x * θ x * sqNormSecondFundamentalForm F₁ x *
          inner ℝ (chartNormal F₁ x) e ∂μ := hjac
    linarith
  -- letting `k → ∞`, then choosing `t` large
  set a := c / 2 * μ.real (ball x₀ r) with ha
  have ha0 : 0 < a := by positivity
  set t : ℝ := 4 * (M + 1) / a with htdef
  have ht : 0 < t := by positivity
  have hlim : Tendsto (fun k ↦ t * ∫ x, ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ +
      t⁻¹ * (2 * ∫ x, ‖fderiv ℝ (η k) x‖ ^ 2 ∂μ + 2 * M)) atTop
      (𝓝 (t * 0 + t⁻¹ * (2 * 0 + 2 * M))) :=
    (hηlim.const_mul t).add (((hηlim.const_mul 2).add_const (2 * M)).const_mul t⁻¹)
  have hle : a ≤ t * 0 + t⁻¹ * (2 * 0 + 2 * M) :=
    ge_of_tendsto hlim (eventually_atTop.mpr ⟨k₀, fun k hk ↦ hkey k hk t ht⟩)
  have hta : t * a = 4 * (M + 1) := by
    rw [htdef]
    field_simp
  have hlt : t⁻¹ * (2 * M) < a := by
    rw [inv_mul_lt_iff₀ ht, hta]
    linarith
  linarith

end SerrinEpigraph
