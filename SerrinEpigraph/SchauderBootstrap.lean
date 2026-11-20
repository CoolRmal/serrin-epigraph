module

public import SerrinEpigraph.LinearSchauder
public import SerrinEpigraph.HolderClasses
public import SerrinEpigraph.DifferenceQuotientRegularity

/-!
# The Schauder bootstrap for linear divergence-form equations

* `holderC_one_of_weakDivFree` (`C^{0,γ}` data → `C^{1,γ/4}`) and `uniform_interior_holder`
  (uniform interior `C^{1,α/4}` bounds for Lipschitz weak solutions of `div (a ∇w) = div G`);
* `fderiv_apply_holder_of_diffQuot`, `holder_partial_of_diffQuot`: limits of difference quotients
  with uniform `C^{1,β}` bounds;
* `IsWeakDivFree.comp_add`, `IsWeakDivFree.diffQuot_linear`: the difference-quotient equations;
* `IsWeakDivFree.fderiv_apply`: directional derivatives of weakly divergence-free `C¹` fields;
* `holderC_two_of_weakDivFree` and `linearRegularity`: `C^{k,γ}` coefficients and right-hand side
  give `C^{k+1,γ'}` solutions (`LinearRegularity d k`), for every `k`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff

namespace SerrinEpigraph

variable {d : ℕ}

/-- A function `C¹` on an open set agrees on any closed ball inside it with a globally Lipschitz
function. -/
theorem exists_lipschitz_eqOn_closedBall {U : Set (Space d)} {u : Space d → ℝ}
    (hu : ContDiffOn ℝ 1 u U) {x : Space d} {R : ℝ} (hxR : closedBall x R ⊆ U) :
    ∃ (K : NNReal) (ũ : Space d → ℝ), LipschitzWith K ũ ∧ EqOn u ũ (closedBall x R) := by
  obtain ⟨K, hK⟩ := (hu.mono hxR).exists_lipschitzOnWith one_ne_zero (convex_closedBall x R)
    (isCompact_closedBall x R)
  obtain ⟨ũ, hũ, heq⟩ := hK.extend_real
  exact ⟨K, ũ, hũ, heq⟩

theorem gradient_eq_of_eqOn_ball {u ũ : Space d → ℝ} {x : Space d} {R : ℝ}
    (heq : EqOn u ũ (closedBall x R)) {y : Space d} (hy : y ∈ ball x R) :
    gradient u y = gradient ũ y := by
  have hev : u =ᶠ[𝓝 y] ũ := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact heq (ball_subset_closedBall hz)
  rw [gradient, gradient, hev.fderiv_eq]

theorem fderiv_eq_of_eqOn_ball {u ũ : Space d → ℝ} {x : Space d} {R : ℝ}
    (heq : EqOn u ũ (closedBall x R)) {y : Space d} (hy : y ∈ ball x R) :
    fderiv ℝ u y = fderiv ℝ ũ y := by
  have hev : u =ᶠ[𝓝 y] ũ := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact heq (ball_subset_closedBall hz)
  exact hev.fderiv_eq

/-- **Local Schauder regularity.** A `C¹` weak solution of `div (a ∇u) = div G` on an open set,
with `a` symmetric, `ν`-elliptic, bounded by `Λ` and locally `γ`-Hölder, and `G` locally
`γ`-Hölder, is `C^{1,γ/4}`. -/
theorem holderC_one_of_weakDivFree (hd : 0 < d) {U : Set (Space d)}
    {a : Space d → Space d →L[ℝ] Space d} {G : Space d → Space d} {u : Space d → ℝ}
    {ν Λ γ : ℝ} (hν : 0 < ν) (hνΛ : ν ≤ Λ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hsymm : ∀ y ∈ U, ∀ v w, inner ℝ (a y v) w = inner ℝ v (a y w))
    (hell : ∀ y ∈ U, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a y ξ) ξ) (hbd : ∀ y ∈ U, ‖a y‖ ≤ Λ)
    (ha : LocHolderOn γ a U) (hG : LocHolderOn γ G U) (hu : ContDiffOn ℝ 1 u U)
    (heq : IsWeakDivFree (fun y ↦ a y (gradient u y) - G y) U) :
    HolderC (γ / 4) U 1 u := by
  refine ⟨hu.differentiableOn one_ne_zero, ?_⟩
  intro x hx
  obtain ⟨ra, hra, hraU, Ma, hMa⟩ := ha x hx
  obtain ⟨rG, hrG, -, MG, hMG⟩ := hG x hx
  set R := min ra rG / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRa : R < ra := by have := min_le_left ra rG; linarith
  have hRG : R < rG := by have := min_le_right ra rG; linarith
  have hxR : closedBall x R ⊆ U := (closedBall_subset_ball hRa).trans hraU
  have hBU : ball x R ⊆ U := ball_subset_closedBall.trans hxR
  obtain ⟨K, ũ, hũ, hũeq⟩ := exists_lipschitz_eqOn_closedBall hu hxR
  have heqũ : IsWeakDivFree (fun y ↦ a y (gradient ũ y) - G y) (ball x R) :=
    (heq.mono hBU).congr_ae (Eventually.of_forall fun y hy ↦ by
      rw [gradient_eq_of_eqOn_ball hũeq hy])
  -- Hölder constants on `ball x R`
  have hHa : ∀ y ∈ ball x R, ∀ y' ∈ ball x R, ‖a y - a y'‖ ≤ max Ma 0 * dist y y' ^ γ :=
    fun y hy y' hy' ↦ (hMa y (ball_subset_ball hRa.le hy) y' (ball_subset_ball hRa.le hy')).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  have hHG : ∀ y ∈ ball x R, ∀ y' ∈ ball x R, ‖G y - G y'‖ ≤ max MG 0 * dist y y' ^ γ :=
    fun y hy y' hy' ↦ (hMG y (ball_subset_ball hRG.le hy) y' (ball_subset_ball hRG.le hy')).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  obtain ⟨C, r₀, hC0, hr₀, hr₀R, hS⟩ :=
    schauder_excess_estimate hd hγ0 hγ1 hν hνΛ hR (le_max_right Ma 0)
  have hS' := hS x a G (max MG 0) ũ K (fun y hy ↦ hsymm y (hBU hy)) (fun y hy ↦ hell y (hBU hy))
    (fun y hy ↦ hbd y (hBU hy)) hHa (le_max_right _ _) hHG hũ heqũ
  -- the Campanato condition for `Dũ`
  set W := ∫ y in ball x R, ‖fderiv ℝ ũ y‖ ^ 2 with hW
  have hW0 : 0 ≤ W := integral_nonneg fun _ ↦ sq_nonneg _
  set ωd := volume.real (ball (0 : Space d) 1) with hωd
  have hωd0 : 0 < ωd := measureReal_unitBall_pos
  set M := Real.sqrt (C * (W + max MG 0 ^ 2) / ωd) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hM2 : M ^ 2 = C * (W + max MG 0 ^ 2) / ωd := Real.sq_sqrt (by positivity)
  have hcamp : ∀ x' ∈ ball x (R / 2), ∀ r, 0 < r → r ≤ r₀ → closedBall x' r ⊆ ball x R →
      ⨍ y in ball x' r, ‖fderiv ℝ ũ y - ⨍ z in ball x' r, fderiv ℝ ũ z‖ ^ 2 ≤
        M ^ 2 * r ^ (2 * (γ / 4)) := by
    intro x' hx' r hr hrr₀ _
    have h1 := hS' x' hx' r hr hrr₀
    rw [setAverage_eq, smul_eq_mul, measureReal_ball_eq_mul x' hr, hM2]
    have hrd : 0 < r ^ d * ωd := by positivity
    have hpow : r ^ ((d : ℝ) + γ / 2) = r ^ d * r ^ (2 * (γ / 4)) := by
      rw [Real.rpow_add hr, Real.rpow_natCast, show (γ / 2) = 2 * (γ / 4) by ring]
    rw [hpow] at h1
    rw [inv_mul_le_iff₀ hrd]
    calc ∫ y in ball x' r, ‖fderiv ℝ ũ y - ⨍ z in ball x' r, fderiv ℝ ũ z‖ ^ 2 ≤
        C * (W + max MG 0 ^ 2) * (r ^ d * r ^ (2 * (γ / 4))) := h1
      _ = r ^ d * ωd * (C * (W + max MG 0 ^ 2) / ωd * r ^ (2 * (γ / 4))) := by
          field_simp
  obtain ⟨-, -, -, hhol⟩ := campanato_fderiv_holder hũ (by linarith : R / 2 ≤ R) hr₀
    (by positivity : 0 < γ / 4) hM0 hcamp
  -- local Hölder continuity of `Du` near `x`
  set ρ := min (R / 8) (r₀ / 4) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρR : ρ ≤ R / 8 := min_le_left _ _
  have hρr : ρ ≤ r₀ / 4 := min_le_right _ _
  refine ⟨ρ, hρ0, (ball_subset_ball (by linarith)).trans hBU,
    campanatoHolderConstant d (γ / 4) * M, fun y hy z hz ↦ ?_⟩
  have hyR : y ∈ ball x (R / 2) := ball_subset_ball (by linarith) hy
  have hzR : z ∈ ball x (R / 2) := ball_subset_ball (by linarith) hz
  have hyz : dist y z < 2 * ρ := by
    have h1 := mem_ball.1 hy
    have h2 := mem_ball.1 hz
    linarith [dist_triangle_right y z x]
  have h2d : 2 * dist y z ≤ r₀ := by linarith
  have hball : closedBall y (2 * dist y z) ⊆ ball x R := by
    intro w hw
    rw [mem_closedBall] at hw
    rw [mem_ball]
    have h1 := mem_ball.1 hy
    linarith [dist_triangle w y x]
  have h := hhol y hyR z hzR h2d hball
  rw [fderiv_eq_of_eqOn_ball hũeq (ball_subset_ball (by linarith) hy),
    fderiv_eq_of_eqOn_ball hũeq (ball_subset_ball (by linarith) hz)]
  exact h

/-- Jensen's inequality for averages: `‖⨍_S f‖² ≤ ⨍_S ‖f‖²`. -/
theorem norm_setAverage_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {S : Set (Space d)} (hS : volume S ≠ ⊤) {f : Space d → E}
    (hf : MemLp f 2 (volume.restrict S)) : ‖⨍ y in S, f y‖ ^ 2 ≤ ⨍ y in S, ‖f y‖ ^ 2 := by
  by_cases hS0 : volume S = 0
  · simp [Measure.restrict_eq_zero.2 hS0]
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS
  have hm : 0 < volume.real S := ENNReal.toReal_pos hS0 hS
  have hf1 : Integrable (fun y ↦ ‖f y‖) (volume.restrict S) := (hf.integrable one_le_two).norm
  have hf2 : Integrable (fun y ↦ ‖f y‖ ^ 2) (volume.restrict S) := hf.norm.integrable_sq
  have hJ := sq_integral_le_measureReal_mul_integral_sq hf1
    (by simpa only [norm_pow, norm_norm] using hf2)
  rw [Measure.real, Measure.restrict_apply_univ] at hJ
  change (∫ y in S, ‖f y‖) ^ 2 ≤ volume.real S * ∫ y in S, ‖f y‖ ^ 2 at hJ
  rw [setAverage_eq, setAverage_eq, norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖∫ y in S, f y‖ ≤ ∫ y in S, ‖f y‖ := norm_integral_le_integral_norm _
  have h2 : (volume.real S)⁻¹ * ‖∫ y in S, f y‖ ≤ (volume.real S)⁻¹ * ∫ y in S, ‖f y‖ :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 0 ≤ (volume.real S)⁻¹ * ‖∫ y in S, f y‖ := by positivity
  calc ((volume.real S)⁻¹ * ‖∫ y in S, f y‖) ^ 2 ≤ ((volume.real S)⁻¹ * ∫ y in S, ‖f y‖) ^ 2 :=
        pow_le_pow_left₀ h3 h2 2
    _ = (volume.real S)⁻¹ ^ 2 * (∫ y in S, ‖f y‖) ^ 2 := by ring
    _ ≤ (volume.real S)⁻¹ ^ 2 * (volume.real S * ∫ y in S, ‖f y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (volume.real S)⁻¹ * ∫ y in S, ‖f y‖ ^ 2 := by field_simp

/-- **Uniform interior `C^{1,α/4}` estimate** for Lipschitz weak solutions with Hölder
coefficients: the constants depend only on `d, α, ν, Λ, H, R`. -/
theorem uniform_interior_holder (hd : 0 < d) {α ν Λ H R : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hν : 0 < ν) (hνΛ : ν ≤ Λ) (hR : 0 < R) (hH : 0 ≤ H) :
    ∃ ρ C₁ C₂ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ (x₀ : Space d) (a : Space d → Space d →L[ℝ] Space d) (G : Space d → Space d) (HG : ℝ)
        (w : Space d → ℝ) (K : NNReal),
        (∀ y ∈ ball x₀ R, ∀ u v, inner ℝ (a y u) v = inner ℝ u (a y v)) →
        (∀ y ∈ ball x₀ R, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a y ξ) ξ) →
        (∀ y ∈ ball x₀ R, ‖a y‖ ≤ Λ) →
        (∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R, ‖a y - a y'‖ ≤ H * dist y y' ^ α) →
        0 ≤ HG →
        (∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R, ‖G y - G y'‖ ≤ HG * dist y y' ^ α) →
        LipschitzWith K w →
        IsWeakDivFree (fun y ↦ a y (gradient w y) - G y) (ball x₀ R) →
        (∀ y ∈ ball x₀ ρ, DifferentiableAt ℝ w y) ∧
        (∀ y ∈ ball x₀ ρ, ‖fderiv ℝ w y‖ ≤
          C₁ * Real.sqrt ((∫ y in ball x₀ R, ‖fderiv ℝ w y‖ ^ 2) + HG ^ 2)) ∧
        (∀ y ∈ ball x₀ ρ, ∀ z ∈ ball x₀ ρ, ‖fderiv ℝ w y - fderiv ℝ w z‖ ≤
          C₂ * Real.sqrt ((∫ y in ball x₀ R, ‖fderiv ℝ w y‖ ^ 2) + HG ^ 2) *
            dist y z ^ (α / 4)) := by
  obtain ⟨C, r₀, hC0, hr₀, hr₀R, hS⟩ := schauder_excess_estimate hd hα0 hα1 hν hνΛ hR hH
  set ωd := volume.real (ball (0 : Space d) 1) with hωd
  have hωd0 : 0 < ωd := measureReal_unitBall_pos
  set ρ := min (R / 8) (r₀ / 4) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρR : ρ ≤ R / 8 := min_le_left _ _
  have hρr : ρ ≤ r₀ / 4 := min_le_right _ _
  have hcc := campanatoConstant_nonneg d (by positivity : 0 < α / 4)
  have hch : 0 ≤ campanatoHolderConstant d (α / 4) := by
    unfold campanatoHolderConstant
    have := Real.sqrt_nonneg ((2 : ℝ) ^ d)
    positivity
  refine ⟨ρ, campanatoConstant d (α / 4) * Real.sqrt (C / ωd) * r₀ ^ (α / 4) +
    1 / Real.sqrt (ωd * r₀ ^ d), campanatoHolderConstant d (α / 4) * Real.sqrt (C / ωd),
    hρ0, by linarith, by positivity, by positivity, ?_⟩
  intro x₀ a G HG w K hsymm hell hbd ha_hol hHG hG_hol hw heq
  have hS' := hS x₀ a G HG w K hsymm hell hbd ha_hol hHG hG_hol hw heq
  set W := ∫ y in ball x₀ R, ‖fderiv ℝ w y‖ ^ 2 with hW
  have hW0 : 0 ≤ W := integral_nonneg fun _ ↦ sq_nonneg _
  set M := Real.sqrt (C * (W + HG ^ 2) / ωd) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hM2 : M ^ 2 = C * (W + HG ^ 2) / ωd := Real.sq_sqrt (by positivity)
  have hMeq : M = Real.sqrt (C / ωd) * Real.sqrt (W + HG ^ 2) := by
    rw [hM, ← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have hcamp : ∀ x' ∈ ball x₀ (R / 2), ∀ r, 0 < r → r ≤ r₀ → closedBall x' r ⊆ ball x₀ R →
      ⨍ y in ball x' r, ‖fderiv ℝ w y - ⨍ z in ball x' r, fderiv ℝ w z‖ ^ 2 ≤
        M ^ 2 * r ^ (2 * (α / 4)) := by
    intro x' hx' r hr hrr₀ _
    have h1 := hS' x' hx' r hr hrr₀
    rw [setAverage_eq, smul_eq_mul, measureReal_ball_eq_mul x' hr, hM2]
    have hrd : 0 < r ^ d * ωd := by positivity
    have hpow : r ^ ((d : ℝ) + α / 2) = r ^ d * r ^ (2 * (α / 4)) := by
      rw [Real.rpow_add hr, Real.rpow_natCast, show (α / 2) = 2 * (α / 4) by ring]
    rw [hpow] at h1
    rw [inv_mul_le_iff₀ hrd]
    calc ∫ y in ball x' r, ‖fderiv ℝ w y - ⨍ z in ball x' r, fderiv ℝ w z‖ ^ 2 ≤
        C * (W + HG ^ 2) * (r ^ d * r ^ (2 * (α / 4))) := h1
      _ = r ^ d * ωd * (C * (W + HG ^ 2) / ωd * r ^ (2 * (α / 4))) := by field_simp
  obtain ⟨hderiv, -, hbound, hhol⟩ := campanato_fderiv_holder hw (by linarith : R / 2 ≤ R) hr₀
    (by positivity : 0 < α / 4) hM0 hcamp
  have hρ2 : ∀ y ∈ ball x₀ ρ, y ∈ ball x₀ (R / 2) := fun y hy ↦
    ball_subset_ball (by linarith) hy
  refine ⟨fun y hy ↦ (hderiv y (hρ2 y hy)).differentiableAt, ?_, ?_⟩
  · intro y hy
    have hball : closedBall y r₀ ⊆ ball x₀ R := by
      intro z hz
      rw [mem_closedBall] at hz
      rw [mem_ball]
      have h1 := mem_ball.1 hy
      linarith [dist_triangle z y x₀]
    have h1 := hbound y (hρ2 y hy) r₀ hr₀ le_rfl hball
    -- the average is controlled by the energy
    have hfin : volume (ball y r₀) ≠ ⊤ := measure_ball_lt_top.ne
    have hL2 := memLp_fderiv_of_lipschitz hw (ball y r₀) hfin
    have hJ := norm_setAverage_sq_le hfin hL2
    have hint : ∫ z in ball y r₀, ‖fderiv ℝ w z‖ ^ 2 ≤ W :=
      setIntegral_mono_set (integrableOn_norm_sq_of_le measure_ball_lt_top.ne measurableSet_ball
        (measurable_fderiv ℝ w).aestronglyMeasurable
        (fun z _ ↦ norm_fderiv_le_of_lipschitz ℝ hw)) (Eventually.of_forall fun _ ↦ sq_nonneg _)
        (ball_subset_closedBall.trans hball).eventuallyLE
    rw [setAverage_eq volume (fun z ↦ ‖fderiv ℝ w z‖ ^ 2) (ball y r₀), smul_eq_mul,
      measureReal_ball_eq_mul y hr₀] at hJ
    have hr0d : 0 < r₀ ^ d * ωd := by positivity
    have havg : ‖⨍ z in ball y r₀, fderiv ℝ w z‖ ≤
        1 / Real.sqrt (ωd * r₀ ^ d) * Real.sqrt (W + HG ^ 2) := by
      have h2 : ‖⨍ z in ball y r₀, fderiv ℝ w z‖ ^ 2 ≤ W / (ωd * r₀ ^ d) := by
        refine hJ.trans ?_
        rw [inv_mul_eq_div, mul_comm (r₀ ^ d)]
        exact div_le_div_of_nonneg_right hint (by positivity)
      have h3 : ‖⨍ z in ball y r₀, fderiv ℝ w z‖ ≤ Real.sqrt (W / (ωd * r₀ ^ d)) :=
        Real.le_sqrt_of_sq_le h2
      refine h3.trans ?_
      rw [Real.sqrt_div' _ (by positivity : 0 ≤ ωd * r₀ ^ d), one_div_mul_eq_div]
      gcongr
      linarith [sq_nonneg HG]
    calc ‖fderiv ℝ w y‖ ≤ ‖fderiv ℝ w y - ⨍ z in ball y r₀, fderiv ℝ w z‖ +
          ‖⨍ z in ball y r₀, fderiv ℝ w z‖ := norm_le_norm_sub_add _ _
      _ ≤ campanatoConstant d (α / 4) * M * r₀ ^ (α / 4) +
          1 / Real.sqrt (ωd * r₀ ^ d) * Real.sqrt (W + HG ^ 2) := add_le_add h1 havg
      _ = (campanatoConstant d (α / 4) * Real.sqrt (C / ωd) * r₀ ^ (α / 4) +
          1 / Real.sqrt (ωd * r₀ ^ d)) * Real.sqrt (W + HG ^ 2) := by rw [hMeq]; ring
  · intro y hy z hz
    have hyz : dist y z < 2 * ρ := by
      have h1 := mem_ball.1 hy
      have h2 := mem_ball.1 hz
      linarith [dist_triangle_right y z x₀]
    have h2d : 2 * dist y z ≤ r₀ := by linarith
    have hball : closedBall y (2 * dist y z) ⊆ ball x₀ R := by
      intro w' hw'
      rw [mem_closedBall] at hw'
      rw [mem_ball]
      have h1 := mem_ball.1 hy
      linarith [dist_triangle w' y x₀]
    have h := hhol y (hρ2 y hy) z (hρ2 z hz) h2d hball
    calc ‖fderiv ℝ w y - fderiv ℝ w z‖ ≤
        campanatoHolderConstant d (α / 4) * M * dist y z ^ (α / 4) := h
      _ = campanatoHolderConstant d (α / 4) * Real.sqrt (C / ωd) * Real.sqrt (W + HG ^ 2) *
          dist y z ^ (α / 4) := by rw [hMeq]; ring

/-! ### Limits of difference quotients -/

/-- **Limits of difference quotients.** If the difference quotients `D_{h_j}^e u` (`h_j → 0`,
`h_j ≠ 0`) are differentiable on a ball with uniformly bounded and uniformly `β`-Hölder
derivatives, then the directional derivative `∂_e u` is differentiable on the ball, and its
derivative is `β`-Hölder with the same constant. -/
theorem fderiv_apply_holder_of_diffQuot {u : Space d → ℝ} {x : Space d} {ρ : ℝ} (e : Space d)
    (hu : ∀ y ∈ ball x ρ, DifferentiableAt ℝ u y) {M M' β : ℝ} (hM : 0 ≤ M) (hβ : 0 < β)
    {hs : ℕ → ℝ} (hs0 : ∀ j, hs j ≠ 0) (hslim : Tendsto hs atTop (𝓝 0))
    (hdiff : ∀ j, ∀ y ∈ ball x ρ, DifferentiableAt ℝ (diffQuot u e (hs j)) y)
    (hbd : ∀ j, ∀ y ∈ ball x ρ, ‖fderiv ℝ (diffQuot u e (hs j)) y‖ ≤ M')
    (hhol : ∀ j, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
      ‖fderiv ℝ (diffQuot u e (hs j)) y - fderiv ℝ (diffQuot u e (hs j)) z‖ ≤
        M * dist y z ^ β) :
    (∀ y ∈ ball x ρ, DifferentiableAt ℝ (fun z ↦ fderiv ℝ u z e) y) ∧
    ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖fderiv ℝ (fun z ↦ fderiv ℝ u z e) y -
      fderiv ℝ (fun z ↦ fderiv ℝ u z e) z‖ ≤ M * dist y z ^ β := by
  obtain ⟨w, hw⟩ : ∃ w : ℕ → Space d → ℝ, w = fun j ↦ diffQuot u e (hs j) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Space d → ℝ, g = fun z ↦ fderiv ℝ u z e := ⟨_, rfl⟩
  rw [← hg]
  have hdiff' : ∀ j, ∀ y ∈ ball x ρ, DifferentiableAt ℝ (w j) y := by rw [hw]; exact hdiff
  have hbd' : ∀ j, ∀ y ∈ ball x ρ, ‖fderiv ℝ (w j) y‖ ≤ M' := by rw [hw]; exact hbd
  have hhol' : ∀ j, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
      ‖fderiv ℝ (w j) y - fderiv ℝ (w j) z‖ ≤ M * dist y z ^ β := by rw [hw]; exact hhol
  -- pointwise convergence of the difference quotients
  have hconv : ∀ y ∈ ball x ρ, Tendsto (fun j ↦ w j y) atTop (𝓝 (g y)) := by
    intro y hy
    have h1 := tendsto_diffQuot (hu y hy) e
    have h2 : Tendsto hs atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hslim, Eventually.of_forall hs0⟩
    rw [hw, hg]
    exact h1.comp h2
  -- first-order expansion with a uniform remainder
  have hexp : ∀ j, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
      |w j z - w j y - fderiv ℝ (w j) y (z - y)| ≤ M * dist z y ^ β * ‖z - y‖ := by
    intro j y hy z hz
    set L := fderiv ℝ (w j) y with hL
    set s := closedBall y (dist z y) ∩ ball x ρ with hs
    have hsc : Convex ℝ s := (convex_closedBall y _).inter (convex_ball x ρ)
    have hys : y ∈ s := ⟨mem_closedBall_self dist_nonneg, hy⟩
    have hzs : z ∈ s := ⟨mem_closedBall.2 le_rfl, hz⟩
    have hdg : ∀ p ∈ s, DifferentiableAt ℝ (fun q ↦ w j q - L q) p := fun p hp ↦
      (hdiff' j p hp.2).sub L.differentiableAt
    have hbdg : ∀ p ∈ s, ‖fderiv ℝ (fun q ↦ w j q - L q) p‖ ≤ M * dist z y ^ β := by
      intro p hp
      rw [fderiv_fun_sub (hdiff' j p hp.2) L.differentiableAt, L.fderiv]
      have hpy : dist p y ≤ dist z y := mem_closedBall.1 hp.1
      calc ‖fderiv ℝ (w j) p - L‖ ≤ M * dist p y ^ β := hhol' j p hp.2 y hy
        _ ≤ M * dist z y ^ β := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg hpy hβ.le) hM
    have h := hsc.norm_image_sub_le_of_norm_fderiv_le hdg hbdg hys hzs
    rw [Real.norm_eq_abs] at h
    calc |w j z - w j y - L (z - y)| = |(w j z - L z) - (w j y - L y)| := by
          rw [map_sub]
          ring_nf
      _ ≤ M * dist z y ^ β * ‖z - y‖ := h
  -- every subsequential limit of the derivatives is the derivative of `g`
  have hkey : ∀ y ∈ ball x ρ, ∀ φ : ℕ → ℕ, StrictMono φ → ∀ L : Space d →L[ℝ] ℝ,
      Tendsto (fun j ↦ fderiv ℝ (w (φ j)) y) atTop (𝓝 L) → HasFDerivAt g L y := by
    intro y hy φ hφ L hL
    have hlim : ∀ z ∈ ball x ρ, |g z - g y - L (z - y)| ≤ M * dist z y ^ β * ‖z - y‖ := by
      intro z hz
      have h3 : Tendsto (fun j ↦ fderiv ℝ (w (φ j)) y (z - y)) atTop (𝓝 (L (z - y))) :=
        ((ContinuousLinearMap.apply ℝ ℝ (z - y)).continuous.tendsto L).comp hL
      have h1 : Tendsto (fun j ↦ w (φ j) z - w (φ j) y - fderiv ℝ (w (φ j)) y (z - y)) atTop
          (𝓝 (g z - g y - L (z - y))) :=
        (((hconv z hz).comp hφ.tendsto_atTop).sub ((hconv y hy).comp hφ.tendsto_atTop)).sub h3
      exact le_of_tendsto' h1.abs (fun j ↦ hexp (φ j) y hy z hz)
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro c hc
    have ht : Tendsto (fun h : Space d ↦ M * ‖h‖ ^ β) (𝓝 0) (𝓝 0) := by
      have h0 : Tendsto (fun h : Space d ↦ ‖h‖) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_norm.tendsto (0 : Space d))
      have := ((Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto).comp h0
      simpa [Real.zero_rpow hβ.ne'] using this.const_mul M
    have hδ : ∀ᶠ h : Space d in 𝓝 0, y + h ∈ ball x ρ := by
      have : Tendsto (fun h : Space d ↦ y + h) (𝓝 0) (𝓝 y) := by
        have := (tendsto_const_nhds (x := y)).add (tendsto_id (x := 𝓝 (0 : Space d)))
        simpa using this
      exact this (isOpen_ball.mem_nhds hy)
    filter_upwards [hδ, ht.eventually (gt_mem_nhds hc)] with h hh hhc
    have h1 := hlim (y + h) hh
    rw [add_sub_cancel_left, dist_eq_norm, add_sub_cancel_left] at h1
    rw [Real.norm_eq_abs]
    exact h1.trans (mul_le_mul_of_nonneg_right hhc.le (norm_nonneg _))
  -- convergent subsequences of the derivatives
  have hsub : ∀ y ∈ ball x ρ, ∀ ψ : ℕ → ℕ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ L : Space d →L[ℝ] ℝ, Tendsto (fun j ↦ fderiv ℝ (w (ψ (φ j))) y) atTop (𝓝 L) := by
    intro y hy ψ
    obtain ⟨L, -, φ, hφ, hL⟩ := (isCompact_closedBall (0 : Space d →L[ℝ] ℝ) M').tendsto_subseq
      (x := fun j ↦ fderiv ℝ (w (ψ j)) y) (fun j ↦ by
        rw [mem_closedBall, dist_zero_right]
        exact hbd' (ψ j) y hy)
    exact ⟨φ, hφ, L, hL⟩
  refine ⟨fun y hy ↦ ?_, fun y hy z hz ↦ ?_⟩
  · obtain ⟨φ, hφ, L, hL⟩ := hsub y hy id
    exact (hkey y hy φ hφ L hL).differentiableAt
  · obtain ⟨φ₁, hφ₁, L₁, hL₁⟩ := hsub y hy id
    obtain ⟨φ₂, hφ₂, L₂, hL₂⟩ := hsub z hz φ₁
    have hL₁' : Tendsto (fun j ↦ fderiv ℝ (w (φ₁ (φ₂ j))) y) atTop (𝓝 L₁) :=
      hL₁.comp hφ₂.tendsto_atTop
    have hd₁ := hkey y hy (φ₁ ∘ φ₂) (hφ₁.comp hφ₂) L₁ hL₁'
    have hd₂ := hkey z hz (φ₁ ∘ φ₂) (hφ₁.comp hφ₂) L₂ hL₂
    rw [hd₁.fderiv, hd₂.fderiv]
    exact le_of_tendsto' (hL₁'.sub hL₂).norm (fun j ↦ hhol' _ y hy z hz)

/-- **Regularity from difference-quotient equations.** If the difference quotients `D_h^e u`
(`0 < |h| < h₀`) are Lipschitz weak solutions of `div (a_h ∇w) = div G_h` in `B_R(x₀)`, with
coefficients satisfying uniform structure and Hölder bounds and with uniformly bounded energies,
then `∂_e u` is differentiable near `x₀` with a Hölder continuous derivative. -/
theorem holder_partial_of_diffQuot (hd : 0 < d) {α ν Λ H R : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hν : 0 < ν) (hνΛ : ν ≤ Λ) (hR : 0 < R) (hH : 0 ≤ H) {x₀ : Space d} {u : Space d → ℝ}
    (e : Space d) (hu : ∀ y ∈ ball x₀ R, DifferentiableAt ℝ u y) {h₀ HG E : ℝ} (hh₀ : 0 < h₀)
    (hHG : 0 ≤ HG) (_hE : 0 ≤ E) (a : ℝ → Space d → Space d →L[ℝ] Space d)
    (G : ℝ → Space d → Space d)
    (hsymm : ∀ h, h ≠ 0 → |h| < h₀ → ∀ y ∈ ball x₀ R, ∀ v w,
      inner ℝ (a h y v) w = inner ℝ v (a h y w))
    (hell : ∀ h, h ≠ 0 → |h| < h₀ → ∀ y ∈ ball x₀ R, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a h y ξ) ξ)
    (hbd : ∀ h, h ≠ 0 → |h| < h₀ → ∀ y ∈ ball x₀ R, ‖a h y‖ ≤ Λ)
    (ha_hol : ∀ h, h ≠ 0 → |h| < h₀ → ∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R,
      ‖a h y - a h y'‖ ≤ H * dist y y' ^ α)
    (hG_hol : ∀ h, h ≠ 0 → |h| < h₀ → ∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R,
      ‖G h y - G h y'‖ ≤ HG * dist y y' ^ α)
    (hLip : ∀ h, h ≠ 0 → ∃ K, LipschitzWith K (diffQuot u e h))
    (heq : ∀ h, h ≠ 0 → |h| < h₀ →
      IsWeakDivFree (fun y ↦ a h y (gradient (diffQuot u e h) y) - G h y) (ball x₀ R))
    (hE' : ∀ h, h ≠ 0 → |h| < h₀ →
      ∫ y in ball x₀ R, ‖fderiv ℝ (diffQuot u e h) y‖ ^ 2 ≤ E) :
    ∃ ρ > 0, ρ ≤ R ∧ ∃ M, 0 ≤ M ∧
      (∀ y ∈ ball x₀ ρ, DifferentiableAt ℝ (fun z ↦ fderiv ℝ u z e) y) ∧
      ∀ y ∈ ball x₀ ρ, ∀ z ∈ ball x₀ ρ, ‖fderiv ℝ (fun z ↦ fderiv ℝ u z e) y -
        fderiv ℝ (fun z ↦ fderiv ℝ u z e) z‖ ≤ M * dist y z ^ (α / 4) := by
  obtain ⟨ρ, C₁, C₂, hρ0, hρR, hC₁, hC₂, hest⟩ :=
    uniform_interior_holder hd hα0 hα1 hν hνΛ hR hH
  set hs : ℕ → ℝ := fun j ↦ h₀ / ((j : ℝ) + 2) with hhs
  have hs0 : ∀ j, hs j ≠ 0 := fun j ↦ by simp only [hhs]; positivity
  have hsh : ∀ j, |hs j| < h₀ := fun j ↦ by
    rw [abs_of_pos (by simp only [hhs]; positivity), hhs, div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hslim : Tendsto hs atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ ↦ ((j : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h2 := h1.inv_tendsto_atTop.const_mul h₀
    simp only [mul_zero] at h2
    refine h2.congr (fun j ↦ ?_)
    simp only [hhs, div_eq_mul_inv, Pi.inv_apply]
  have hsq : ∀ j, Real.sqrt ((∫ y in ball x₀ R, ‖fderiv ℝ (diffQuot u e (hs j)) y‖ ^ 2) +
      HG ^ 2) ≤ Real.sqrt (E + HG ^ 2) := fun j ↦
    Real.sqrt_le_sqrt (by linarith [hE' (hs j) (hs0 j) (hsh j)])
  have hall : ∀ j, (∀ y ∈ ball x₀ ρ, DifferentiableAt ℝ (diffQuot u e (hs j)) y) ∧
      (∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (diffQuot u e (hs j)) y‖ ≤ C₁ * Real.sqrt (E + HG ^ 2)) ∧
      (∀ y ∈ ball x₀ ρ, ∀ z ∈ ball x₀ ρ, ‖fderiv ℝ (diffQuot u e (hs j)) y -
        fderiv ℝ (diffQuot u e (hs j)) z‖ ≤ C₂ * Real.sqrt (E + HG ^ 2) * dist y z ^ (α / 4)) := by
    intro j
    obtain ⟨K, hK⟩ := hLip (hs j) (hs0 j)
    obtain ⟨h1, h2, h3⟩ := hest x₀ (a (hs j)) (G (hs j)) HG (diffQuot u e (hs j)) K
      (hsymm _ (hs0 j) (hsh j)) (hell _ (hs0 j) (hsh j)) (hbd _ (hs0 j) (hsh j))
      (ha_hol _ (hs0 j) (hsh j)) hHG (hG_hol _ (hs0 j) (hsh j)) hK (heq _ (hs0 j) (hsh j))
    refine ⟨h1, fun y hy ↦ (h2 y hy).trans (mul_le_mul_of_nonneg_left (hsq j) hC₁),
      fun y hy z hz ↦ (h3 y hy z hz).trans ?_⟩
    have := Real.rpow_nonneg (dist_nonneg (x := y) (y := z)) (α / 4)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsq j) hC₂) this
  obtain ⟨hdiff, hhol⟩ := fderiv_apply_holder_of_diffQuot (x := x₀) (ρ := ρ) e
    (fun y hy ↦ hu y (ball_subset_ball hρR hy)) (by positivity : 0 ≤ C₂ * Real.sqrt (E + HG ^ 2))
    (by positivity : 0 < α / 4) hs0 hslim (fun j ↦ (hall j).1) (fun j ↦ (hall j).2.1)
    (fun j ↦ (hall j).2.2)
  exact ⟨ρ, hρ0, hρR, C₂ * Real.sqrt (E + HG ^ 2), by positivity, hdiff, hhol⟩

/-! ### Algebra of weakly divergence-free fields -/

theorem integrable_inner_gradient_of_locallyIntegrableOn {U : Set (Space d)}
    {V : Space d → Space d} (hV : LocallyIntegrableOn V U) {ψ : Space d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
    Integrable (fun y ↦ inner ℝ (V y) (gradient ψ y)) := by
  have hi : IntegrableOn V (tsupport ψ) := hV.integrableOn_compact_subset hψU hc
  have hgm : Measurable (gradient ψ) :=
    (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ ψ)
  have h1 : IntegrableOn (fun y ↦ inner ℝ (V y) (gradient ψ y)) (tsupport ψ) := by
    refine (hi.norm.mul_const (K : ℝ)).mono' (hi.aestronglyMeasurable.inner
      hgm.aestronglyMeasurable) (Eventually.of_forall fun y ↦ ?_)
    calc ‖inner ℝ (V y) (gradient ψ y)‖ ≤ ‖V y‖ * ‖gradient ψ y‖ := norm_inner_le_norm _ _
      _ ≤ ‖V y‖ * K := mul_le_mul_of_nonneg_left (by
          rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hψ)
          (norm_nonneg _)
  exact h1.integrable_of_forall_notMem_eq_zero (fun y hy ↦ by
    rw [gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right])

theorem IsWeakDivFree.sub' {U : Set (Space d)} {V W : Space d → Space d}
    (hV : LocallyIntegrableOn V U) (hW : LocallyIntegrableOn W U) (h₁ : IsWeakDivFree V U)
    (h₂ : IsWeakDivFree W U) : IsWeakDivFree (fun y ↦ V y - W y) U := by
  rintro ψ ⟨K, hψ⟩ hc hψU
  have e : (fun y ↦ inner ℝ (V y - W y) (gradient ψ y)) =
      fun y ↦ inner ℝ (V y) (gradient ψ y) - inner ℝ (W y) (gradient ψ y) := by
    funext y
    exact inner_sub_left _ _ _
  rw [e, integral_sub (integrable_inner_gradient_of_locallyIntegrableOn hV hψ hc hψU)
    (integrable_inner_gradient_of_locallyIntegrableOn hW hψ hc hψU), h₁ ψ ⟨K, hψ⟩ hc hψU,
    h₂ ψ ⟨K, hψ⟩ hc hψU, sub_zero]

theorem IsWeakDivFree.const_smul {U : Set (Space d)} {V : Space d → Space d}
    (h : IsWeakDivFree V U) (c : ℝ) : IsWeakDivFree (fun y ↦ c • V y) U := by
  intro ψ hψ hc hψU
  simp_rw [real_inner_smul_left]
  rw [integral_const_mul, h ψ hψ hc hψU, mul_zero]

/-- Translates of weakly divergence-free fields are weakly divergence free. -/
theorem IsWeakDivFree.comp_add {U : Set (Space d)} {V : Space d → Space d}
    (h : IsWeakDivFree V U) (z : Space d) :
    IsWeakDivFree (fun y ↦ V (y + z)) ((· + z) ⁻¹' U) := by
  rintro φ ⟨K, hφ⟩ hφc hsub
  let ψ : Space d → ℝ := φ ∘ (Homeomorph.addRight (-z))
  have hψ : LipschitzWith K ψ := by
    refine LipschitzWith.of_dist_le_mul fun y y' ↦ ?_
    have := hφ.dist_le_mul (y + -z) (y' + -z)
    simpa [ψ, dist_add_right] using this
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph _
  have hψs : tsupport ψ ⊆ U := by
    rw [tsupport_comp_eq_preimage]
    intro y hy
    have h := hsub hy
    simpa using h
  have hgrad : ∀ y, gradient ψ y = gradient φ (y - z) := by
    intro y
    have hfun : ψ = fun y ↦ φ (y + -z) := rfl
    simp only [gradient, hfun, fderiv_comp_add_right, sub_eq_add_neg]
  have h0 := h ψ ⟨K, hψ⟩ hψc hψs
  simp_rw [hgrad] at h0
  have he := integral_add_right_eq_self (μ := volume)
    (fun y ↦ inner ℝ (V y) (gradient φ (y - z))) z
  simp only [add_sub_cancel_right] at he
  rw [he]
  exact h0

/-- **Difference quotients of solutions of linear equations.** If `div (a ∇u) = div G` weakly in
`U`, then `w = D_h^e u` solves `div (a(· + h e) ∇w) = div G_h` in every `W ⊆ U ∩ (U - h e)`,
`G_h = h⁻¹ (G(· + h e) - G) - h⁻¹ (a(· + h e) - a) ∇u`. -/
theorem IsWeakDivFree.diffQuot_linear {U : Set (Space d)} {a : Space d → Space d →L[ℝ] Space d}
    {G : Space d → Space d} {u : Space d → ℝ} {K : NNReal} (hu : LipschitzWith K u)
    (heq : IsWeakDivFree (fun y ↦ a y (gradient u y) - G y) U) (e : Space d) {h : ℝ}
    (_hh : h ≠ 0) {W : Set (Space d)} (hWU : W ⊆ U) (hWh : W ⊆ (· + h • e) ⁻¹' U)
    (hV : LocallyIntegrableOn (fun y ↦ a y (gradient u y) - G y) W)
    (hVh : LocallyIntegrableOn (fun y ↦ a (y + h • e) (gradient u (y + h • e)) - G (y + h • e)) W) :
    IsWeakDivFree (fun y ↦ a (y + h • e) (gradient (diffQuot u e h) y) -
      (h⁻¹ • (G (y + h • e) - G y) - h⁻¹ • (a (y + h • e) - a y) (gradient u y))) W := by
  have h1 := heq.mono hWU
  have h2 := (heq.comp_add (h • e)).mono hWh
  have h3 := (IsWeakDivFree.sub' hVh hV h2 h1).const_smul h⁻¹
  refine h3.congr_ae ?_
  have h0 := hu.ae_differentiableAt (μ := volume)
  have h0' : ∀ᵐ y, DifferentiableAt ℝ u (y + h • e) :=
    (measurePreserving_add_right volume (h • e)).quasiMeasurePreserving.ae h0
  filter_upwards [h0, h0'] with y hy0 hy1 _
  rw [gradient_diffQuot hy0 hy1]
  simp only [map_smul, sub_apply, smul_sub, map_sub]
  abel

/-! ### Hölder bounds for difference quotients -/

/-- If `Df` is `γ`-Hölder on a convex set containing the relevant segments, then the difference
quotients `D_h^e f` are `γ`-Hölder with the same constant (for `‖e‖ ≤ 1`). -/
theorem norm_diffQuot_sub_diffQuot_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space d → F} {S : Set (Space d)} (hS : Convex ℝ S)
    (hf : ∀ y ∈ S, DifferentiableAt ℝ f y) {H γ : ℝ} (hH : 0 ≤ H)
    (hhol : ∀ y ∈ S, ∀ z ∈ S, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ H * dist y z ^ γ)
    {e : Space d} (he : ‖e‖ ≤ 1) {h : ℝ} (hh : h ≠ 0) {y y' : Space d}
    (hy : y ∈ S) (hy' : y' ∈ S) (hyh : y + h • e ∈ S) (hyh' : y' + h • e ∈ S) :
    ‖h⁻¹ • (f (y + h • e) - f y) - h⁻¹ • (f (y' + h • e) - f y')‖ ≤ H * dist y y' ^ γ := by
  set c := y' - y with hc
  set g : Space d → F := fun z ↦ f z - f (z + c) with hg
  have hseg : ∀ z ∈ segment ℝ y (y + h • e), z ∈ S ∧ z + c ∈ S := by
    intro z hz
    refine ⟨hS.segment_subset hy hyh hz, ?_⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have hmem := hS hy' hyh' ha hb hab
    obtain rfl : b = 1 - a := by linarith
    have e1 : a • y + (1 - a) • (y + h • e) + c = a • y' + (1 - a) • (y' + h • e) := by
      rw [hc]
      simp only [smul_add, sub_smul, one_smul]
      abel
    rw [e1]
    exact hmem
  have hdc : ∀ z ∈ segment ℝ y (y + h • e), DifferentiableAt ℝ (fun w ↦ f (w + c)) z :=
    fun z hz ↦ (differentiableAt_comp_add_right c).2 (hf _ (hseg z hz).2)
  have hdg : ∀ z ∈ segment ℝ y (y + h • e), DifferentiableAt ℝ g z := fun z hz ↦
    (hf z (hseg z hz).1).sub (hdc z hz)
  have hbd : ∀ z ∈ segment ℝ y (y + h • e), ‖fderiv ℝ g z‖ ≤ H * dist y y' ^ γ := by
    intro z hz
    have h1 : fderiv ℝ g z = fderiv ℝ f z - fderiv ℝ f (z + c) := by
      rw [hg, fderiv_fun_sub (hf z (hseg z hz).1) (hdc z hz), fderiv_comp_add_right]
    rw [h1]
    have h2 := hhol z (hseg z hz).1 (z + c) (hseg z hz).2
    have h3 : dist z (z + c) = dist y y' := by
      rw [dist_eq_norm, show z - (z + c) = -c by abel, norm_neg, hc, ← dist_eq_norm, dist_comm]
    rwa [h3] at h2
  have hmv := (convex_segment y (y + h • e)).norm_image_sub_le_of_norm_fderiv_le hdg hbd
    (left_mem_segment ℝ y (y + h • e)) (right_mem_segment ℝ y (y + h • e))
  have hkey : h⁻¹ • (f (y + h • e) - f y) - h⁻¹ • (f (y' + h • e) - f y') =
      h⁻¹ • (g (y + h • e) - g y) := by
    have hy'c : y' = y + c := by rw [hc]; abel
    rw [hy'c, add_right_comm y c (h • e), ← smul_sub]
    congr 1
    simp only [hg]
    abel
  rw [hkey, norm_smul, norm_inv, Real.norm_eq_abs]
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hmv
  have hhe : |h| * ‖e‖ ≤ |h| := mul_le_of_le_one_right (abs_nonneg h) he
  have hpos : 0 < |h| := abs_pos.2 hh
  have hHd : 0 ≤ H * dist y y' ^ γ := mul_nonneg hH (Real.rpow_nonneg dist_nonneg _)
  calc |h|⁻¹ * ‖g (y + h • e) - g y‖ ≤ |h|⁻¹ * (H * dist y y' ^ γ * (|h| * ‖e‖)) :=
        mul_le_mul_of_nonneg_left hmv (by positivity)
    _ ≤ |h|⁻¹ * (H * dist y y' ^ γ * |h|) := by gcongr
    _ = H * dist y y' ^ γ := by field_simp

theorem norm_diffQuot_le_of_fderiv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space d → F} {S : Set (Space d)} (hS : Convex ℝ S)
    (hf : ∀ y ∈ S, DifferentiableAt ℝ f y) {C : ℝ} (hC : ∀ y ∈ S, ‖fderiv ℝ f y‖ ≤ C)
    {e : Space d} (he : ‖e‖ ≤ 1) {h : ℝ} (hh : h ≠ 0) {y : Space d} (hy : y ∈ S)
    (hyh : y + h • e ∈ S) : ‖h⁻¹ • (f (y + h • e) - f y)‖ ≤ C := by
  have h1 := hS.norm_image_sub_le_of_norm_fderiv_le hf hC hy hyh
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC y hy)
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  have hpos : 0 < |h| := abs_pos.2 hh
  calc |h|⁻¹ * ‖f (y + h • e) - f y‖ ≤ |h|⁻¹ * (C * (|h| * ‖e‖)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ |h|⁻¹ * (C * |h|) := by
        gcongr
        exact mul_le_of_le_one_right (abs_nonneg h) he
    _ = C := by field_simp

/-- Bounds for the right-hand sides of the difference-quotient equations. -/
theorem diffQuot_rhs_bounds {S : Set (Space d)} (hS : Convex ℝ S)
    {a : Space d → Space d →L[ℝ] Space d} {G : Space d → Space d} {u : Space d → ℝ}
    {Ku : NNReal} (hu : LipschitzWith Ku u) {γ Hda HdG Hu Ca CG : ℝ}
    (hHda : 0 ≤ Hda) (hHdG : 0 ≤ HdG) (hCa : 0 ≤ Ca)
    (ha_diff : ∀ y ∈ S, DifferentiableAt ℝ a y) (hG_diff : ∀ y ∈ S, DifferentiableAt ℝ G y)
    (hda_hol : ∀ y ∈ S, ∀ z ∈ S, ‖fderiv ℝ a y - fderiv ℝ a z‖ ≤ Hda * dist y z ^ γ)
    (hdG_hol : ∀ y ∈ S, ∀ z ∈ S, ‖fderiv ℝ G y - fderiv ℝ G z‖ ≤ HdG * dist y z ^ γ)
    (hda_bd : ∀ y ∈ S, ‖fderiv ℝ a y‖ ≤ Ca) (hdG_bd : ∀ y ∈ S, ‖fderiv ℝ G y‖ ≤ CG)
    (hu_hol : ∀ y ∈ S, ∀ z ∈ S, ‖fderiv ℝ u y - fderiv ℝ u z‖ ≤ Hu * dist y z ^ γ)
    {e : Space d} (he : ‖e‖ ≤ 1) {h : ℝ} (hh : h ≠ 0) {y y' : Space d} (hy : y ∈ S)
    (hy' : y' ∈ S) (hyh : y + h • e ∈ S) (hyh' : y' + h • e ∈ S) :
    ‖h⁻¹ • (G (y + h • e) - G y) - h⁻¹ • (a (y + h • e) - a y) (gradient u y)‖ ≤
        CG + Ca * Ku ∧
      ‖(h⁻¹ • (G (y + h • e) - G y) - h⁻¹ • (a (y + h • e) - a y) (gradient u y)) -
        (h⁻¹ • (G (y' + h • e) - G y') - h⁻¹ • (a (y' + h • e) - a y') (gradient u y'))‖ ≤
        (HdG + Hda * Ku + Ca * Hu) * dist y y' ^ γ := by
  have hgradK : ∀ z, ‖gradient u z‖ ≤ Ku := fun z ↦ by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hu
  have hDa : ∀ z ∈ S, z + h • e ∈ S → ‖h⁻¹ • (a (z + h • e) - a z)‖ ≤ Ca := fun z hz hzh ↦
    norm_diffQuot_le_of_fderiv_le hS ha_diff hda_bd he hh hz hzh
  have hDG : ‖h⁻¹ • (G (y + h • e) - G y)‖ ≤ CG :=
    norm_diffQuot_le_of_fderiv_le hS hG_diff hdG_bd he hh hy hyh
  have happ : ∀ z ∈ S, z + h • e ∈ S →
      ‖h⁻¹ • (a (z + h • e) - a z) (gradient u z)‖ ≤ Ca * Ku := by
    intro z hz hzh
    rw [← smul_apply]
    exact ((h⁻¹ • (a (z + h • e) - a z)).le_opNorm _).trans
      (mul_le_mul (hDa z hz hzh) (hgradK z) (norm_nonneg _) hCa)
  refine ⟨(norm_sub_le _ _).trans (add_le_add hDG (happ y hy hyh)), ?_⟩
  have h1 := norm_diffQuot_sub_diffQuot_le hS hG_diff hHdG hdG_hol he hh hy hy' hyh hyh'
  have h2 := norm_diffQuot_sub_diffQuot_le hS ha_diff hHda hda_hol he hh hy hy' hyh hyh'
  have h3 : ‖gradient u y - gradient u y'‖ ≤ Hu * dist y y' ^ γ := by
    rw [gradient, gradient, ← map_sub, LinearIsometryEquiv.norm_map]
    exact hu_hol y hy y' hy'
  set A₁ := h⁻¹ • (a (y + h • e) - a y) with hA₁
  set A₂ := h⁻¹ • (a (y' + h • e) - a y') with hA₂
  have h4 : ‖A₁ (gradient u y) - A₂ (gradient u y')‖ ≤
      Hda * dist y y' ^ γ * Ku + Ca * (Hu * dist y y' ^ γ) := by
    calc ‖A₁ (gradient u y) - A₂ (gradient u y')‖ =
        ‖(A₁ - A₂) (gradient u y) + A₂ (gradient u y - gradient u y')‖ := by
          rw [sub_apply, map_sub]
          congr 1
          abel
      _ ≤ ‖(A₁ - A₂) (gradient u y)‖ + ‖A₂ (gradient u y - gradient u y')‖ := norm_add_le _ _
      _ ≤ ‖A₁ - A₂‖ * ‖gradient u y‖ + ‖A₂‖ * ‖gradient u y - gradient u y'‖ :=
          add_le_add ((A₁ - A₂).le_opNorm _) (A₂.le_opNorm _)
      _ ≤ Hda * dist y y' ^ γ * Ku + Ca * (Hu * dist y y' ^ γ) := by
          have := Real.rpow_nonneg (dist_nonneg (x := y) (y := y')) γ
          gcongr
          · exact hgradK y
          · exact hDa y' hy' hyh'
  have e1 : h⁻¹ • (a (y + h • e) - a y) (gradient u y) = A₁ (gradient u y) := by
    rw [hA₁, smul_apply]
  have e2 : h⁻¹ • (a (y' + h • e) - a y') (gradient u y') = A₂ (gradient u y') := by
    rw [hA₂, smul_apply]
  rw [e1, e2]
  calc ‖(h⁻¹ • (G (y + h • e) - G y) - A₁ (gradient u y)) -
        (h⁻¹ • (G (y' + h • e) - G y') - A₂ (gradient u y'))‖ =
      ‖(h⁻¹ • (G (y + h • e) - G y) - h⁻¹ • (G (y' + h • e) - G y')) -
        (A₁ (gradient u y) - A₂ (gradient u y'))‖ := by
        congr 1
        abel
    _ ≤ ‖h⁻¹ • (G (y + h • e) - G y) - h⁻¹ • (G (y' + h • e) - G y')‖ +
        ‖A₁ (gradient u y) - A₂ (gradient u y')‖ := norm_sub_le _ _
    _ ≤ HdG * dist y y' ^ γ + (Hda * dist y y' ^ γ * Ku + Ca * (Hu * dist y y' ^ γ)) :=
        add_le_add h1 h4
    _ = (HdG + Hda * Ku + Ca * Hu) * dist y y' ^ γ := by ring

theorem aestronglyMeasurable_diffQuot_rhs {W U : Set (Space d)} (hW : MeasurableSet W)
    {a : Space d → Space d →L[ℝ] Space d} {G : Space d → Space d} {u : Space d → ℝ}
    (ha : ContinuousOn a U) (hG : ContinuousOn G U) (hWU : W ⊆ U) {e : Space d} {h : ℝ}
    (hmaps : MapsTo (fun y ↦ y + h • e) W U) :
    AEStronglyMeasurable (fun y ↦ h⁻¹ • (G (y + h • e) - G y) -
      h⁻¹ • (a (y + h • e) - a y) (gradient u y)) (volume.restrict W) := by
  have hgm : Measurable (gradient u) :=
    (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ u)
  have hca : ContinuousOn (fun y ↦ a (y + h • e)) W :=
    ha.comp (continuous_id.add continuous_const).continuousOn hmaps
  have hcG : ContinuousOn (fun y ↦ G (y + h • e)) W :=
    hG.comp (continuous_id.add continuous_const).continuousOn hmaps
  have hG1 : AEStronglyMeasurable (fun y ↦ G (y + h • e) - G y) (volume.restrict W) :=
    (hcG.aestronglyMeasurable hW).sub ((hG.mono hWU).aestronglyMeasurable hW)
  have ha1 : AEStronglyMeasurable (fun y ↦ a (y + h • e) - a y) (volume.restrict W) :=
    (hca.aestronglyMeasurable hW).sub ((ha.mono hWU).aestronglyMeasurable hW)
  have ha2 : AEStronglyMeasurable (fun y ↦ (a (y + h • e) - a y) (gradient u y))
      (volume.restrict W) :=
    (ContinuousLinearMap.id ℝ (Space d →L[ℝ] Space d)).aestronglyMeasurable_comp₂ ha1
      hgm.aestronglyMeasurable
  exact (hG1.const_smul h⁻¹).sub (ha2.const_smul h⁻¹)

/-- **Second-order regularity for linear equations with `C^{1,γ}` data** (on a ball, one
direction at a time). -/
theorem linear_partial_holder_ball (hd : 0 < d) {u : Space d → ℝ} {Ku : NNReal}
    (hu : LipschitzWith Ku u) {x₀ : Space d} {R₀ : ℝ} (hR₀ : 0 < R₀)
    {a : Space d → Space d →L[ℝ] Space d} {G : Space d → Space d}
    {ν Λ γ Ha Hda HdG Hu Ca CG : ℝ} (hν : 0 < ν) (hνΛ : ν ≤ Λ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hHa : 0 ≤ Ha) (hHda : 0 ≤ Hda) (hHdG : 0 ≤ HdG) (hHu : 0 ≤ Hu) (hCa : 0 ≤ Ca)
    (hCG : 0 ≤ CG)
    (hsymm : ∀ y ∈ ball x₀ R₀, ∀ v w, inner ℝ (a y v) w = inner ℝ v (a y w))
    (hell : ∀ y ∈ ball x₀ R₀, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a y ξ) ξ)
    (hbd : ∀ y ∈ ball x₀ R₀, ‖a y‖ ≤ Λ)
    (ha_diff : ∀ y ∈ ball x₀ R₀, DifferentiableAt ℝ a y)
    (hG_diff : ∀ y ∈ ball x₀ R₀, DifferentiableAt ℝ G y)
    (ha_hol : ∀ y ∈ ball x₀ R₀, ∀ z ∈ ball x₀ R₀, ‖a y - a z‖ ≤ Ha * dist y z ^ γ)
    (hda_hol : ∀ y ∈ ball x₀ R₀, ∀ z ∈ ball x₀ R₀,
      ‖fderiv ℝ a y - fderiv ℝ a z‖ ≤ Hda * dist y z ^ γ)
    (hdG_hol : ∀ y ∈ ball x₀ R₀, ∀ z ∈ ball x₀ R₀,
      ‖fderiv ℝ G y - fderiv ℝ G z‖ ≤ HdG * dist y z ^ γ)
    (hda_bd : ∀ y ∈ ball x₀ R₀, ‖fderiv ℝ a y‖ ≤ Ca)
    (hdG_bd : ∀ y ∈ ball x₀ R₀, ‖fderiv ℝ G y‖ ≤ CG)
    (hu_diff : ∀ y ∈ ball x₀ R₀, DifferentiableAt ℝ u y)
    (hu_hol : ∀ y ∈ ball x₀ R₀, ∀ z ∈ ball x₀ R₀,
      ‖fderiv ℝ u y - fderiv ℝ u z‖ ≤ Hu * dist y z ^ γ)
    (heq : IsWeakDivFree (fun y ↦ a y (gradient u y) - G y) (ball x₀ R₀))
    {e : Space d} (he : ‖e‖ ≤ 1) :
    ∃ ρ > 0, ∃ M, 0 ≤ M ∧
      (∀ y ∈ ball x₀ ρ, DifferentiableAt ℝ (fun z ↦ fderiv ℝ u z e) y) ∧
      ∀ y ∈ ball x₀ ρ, ∀ z ∈ ball x₀ ρ, ‖fderiv ℝ (fun z ↦ fderiv ℝ u z e) y -
        fderiv ℝ (fun z ↦ fderiv ℝ u z e) z‖ ≤ M * dist y z ^ (γ / 4) := by
  obtain ⟨R, hRdef⟩ : ∃ R, R = R₀ / 4 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have hUc : Convex ℝ (ball x₀ R₀) := convex_ball x₀ R₀
  have hshift : ∀ h, |h| < R → ∀ y ∈ ball x₀ (2 * R), y + h • e ∈ ball x₀ R₀ := by
    intro h hh y hy
    rw [mem_ball] at hy ⊢
    have h1 : ‖h • e‖ ≤ |h| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg h) he
    calc dist (y + h • e) x₀ ≤ dist y x₀ + ‖h • e‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
          exact norm_add_le _ _
      _ < R₀ := by rw [hRdef] at hy hh; linarith
  have hW : ball x₀ (2 * R) ⊆ ball x₀ R₀ := ball_subset_ball (by rw [hRdef]; linarith)
  have hRW : ball x₀ R ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  have ha_cont : ContinuousOn a (ball x₀ R₀) := fun y hy ↦
    (ha_diff y hy).continuousAt.continuousWithinAt
  have hG_cont : ContinuousOn G (ball x₀ R₀) := fun y hy ↦
    (hG_diff y hy).continuousAt.continuousWithinAt
  have hgm : Measurable (gradient u) :=
    (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ u)
  have hgradK : ∀ y, ‖gradient u y‖ ≤ Ku := fun y ↦ by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hu
  -- a bound for `G` on the ball
  have hGb : ∀ y ∈ ball x₀ R₀, ‖G y‖ ≤ ‖G x₀‖ + CG * R₀ := by
    intro y hy
    have h1 := hUc.norm_image_sub_le_of_norm_fderiv_le hG_diff hdG_bd (mem_ball_self hR₀) hy
    have h2 : ‖y - x₀‖ ≤ R₀ := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
    have h3 := norm_sub_norm_le (G y) (G x₀)
    have h4 : CG * ‖y - x₀‖ ≤ CG * R₀ := mul_le_mul_of_nonneg_left h2 hCG
    linarith
  -- local integrability of the fluxes
  have hfinW : volume (ball x₀ (2 * R)) ≠ ⊤ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball x₀ (2 * R))) := isFiniteMeasure_restrict.2 hfinW
  have hflux : ∀ c : Space d, MapsTo (fun y ↦ y + c) (ball x₀ (2 * R)) (ball x₀ R₀) →
      LocallyIntegrableOn (fun y ↦ a (y + c) (gradient u (y + c)) - G (y + c))
        (ball x₀ (2 * R)) := by
    intro c hmaps
    have hca : ContinuousOn (fun y ↦ a (y + c)) (ball x₀ (2 * R)) :=
      ha_cont.comp (continuous_id.add continuous_const).continuousOn hmaps
    have hcG : ContinuousOn (fun y ↦ G (y + c)) (ball x₀ (2 * R)) :=
      hG_cont.comp (continuous_id.add continuous_const).continuousOn hmaps
    refine IntegrableOn.locallyIntegrableOn ?_
    refine (integrable_const (Λ * Ku + (‖G x₀‖ + CG * R₀))).mono' ?_ ?_
    · exact ((ContinuousLinearMap.id ℝ (Space d →L[ℝ] Space d)).aestronglyMeasurable_comp₂
        (hca.aestronglyMeasurable measurableSet_ball)
        (hgm.comp (measurable_add_const c)).aestronglyMeasurable).sub
        (hcG.aestronglyMeasurable measurableSet_ball)
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have hy' := hmaps hy
      have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hbd _ hy')
      calc ‖a (y + c) (gradient u (y + c)) - G (y + c)‖ ≤
          ‖a (y + c) (gradient u (y + c))‖ + ‖G (y + c)‖ := norm_sub_le _ _
        _ ≤ Λ * Ku + (‖G x₀‖ + CG * R₀) := add_le_add (((a _).le_opNorm _).trans
            (mul_le_mul (hbd _ hy') (hgradK _) (norm_nonneg _) hΛ0)) (hGb _ hy')
  have hV0 : LocallyIntegrableOn (fun y ↦ a y (gradient u y) - G y) (ball x₀ (2 * R)) := by
    have := hflux 0 (fun y hy ↦ by simpa using hW hy)
    simpa using this
  set Gh : ℝ → Space d → Space d := fun h y ↦ h⁻¹ • (G (y + h • e) - G y) -
    h⁻¹ • (a (y + h • e) - a y) (gradient u y) with hGh
  have hDQeq : ∀ h, h ≠ 0 → |h| < R → IsWeakDivFree
      (fun y ↦ a (y + h • e) (gradient (diffQuot u e h) y) - Gh h y) (ball x₀ (2 * R)) :=
    fun h hh hhR ↦ IsWeakDivFree.diffQuot_linear hu heq e hh hW
      (fun y hy ↦ hshift h hhR y hy) hV0 (hflux (h • e) (fun y hy ↦ hshift h hhR y hy))
  have hGh_bd : ∀ h, h ≠ 0 → |h| < R → ∀ y ∈ ball x₀ (2 * R), ‖Gh h y‖ ≤ CG + Ca * Ku :=
    fun h hh hhR y hy ↦ (diffQuot_rhs_bounds hUc hu hHda hHdG hCa ha_diff hG_diff hda_hol
      hdG_hol hda_bd hdG_bd hu_hol he hh (hW hy) (hW hy) (hshift h hhR y hy)
      (hshift h hhR y hy)).1
  have hGh_hol : ∀ h, h ≠ 0 → |h| < R → ∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R,
      ‖Gh h y - Gh h y'‖ ≤ (HdG + Hda * Ku + Ca * Hu) * dist y y' ^ γ :=
    fun h hh hhR y hy y' hy' ↦ (diffQuot_rhs_bounds hUc hu hHda hHdG hCa ha_diff hG_diff
      hda_hol hdG_hol hda_bd hdG_bd hu_hol he hh (hW (hRW hy)) (hW (hRW hy'))
      (hshift h hhR y (hRW hy)) (hshift h hhR y' (hRW hy'))).2
  -- uniform energy bounds
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = 2 / ν * ((4 * Λ ^ 2 / ν + 1) * (2 / (2 * R - R)) ^ 2 *
      ((Ku : ℝ) ^ 2 * volume.real (ball x₀ (2 * R))) +
        (1 / ν + 1) * ((CG + Ca * Ku) ^ 2 * volume.real (ball x₀ (2 * R)))) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    have := measureReal_nonneg (μ := volume) (s := ball x₀ (2 * R))
    rw [hEdef]
    positivity
  have hE : ∀ h, h ≠ 0 → |h| < R →
      ∫ y in ball x₀ R, ‖fderiv ℝ (diffQuot u e h) y‖ ^ 2 ≤ E := by
    intro h hh hhR
    have hmaps : MapsTo (fun y ↦ y + h • e) (ball x₀ (2 * R)) (ball x₀ R₀) := fun y hy ↦
      hshift h hhR y hy
    have hca : ContinuousOn (fun y ↦ a (y + h • e)) (ball x₀ (2 * R)) :=
      ha_cont.comp (continuous_id.add continuous_const).continuousOn hmaps
    have hGhm : AEStronglyMeasurable (Gh h) (volume.restrict (ball x₀ (2 * R))) :=
      aestronglyMeasurable_diffQuot_rhs measurableSet_ball ha_cont hG_cont hW hmaps
    have hGhL2 : MemLp (Gh h) 2 (volume.restrict (ball x₀ (2 * R))) :=
      MemLp.of_bound hGhm (CG + Ca * Ku) ((ae_restrict_iff' measurableSet_ball).2
        (Eventually.of_forall fun y hy ↦ hGh_bd h hh hhR y hy))
    have hcac := caccioppoli (a := fun y ↦ a (y + h • e)) (Λ := Λ) hν (x₀ := x₀) (ρ := R)
      (s := 2 * R) (by linarith) (hca.aestronglyMeasurable measurableSet_ball)
      (fun y hy ξ ↦ hell _ (hshift h hhR y hy) ξ) (fun y hy ↦ hbd _ (hshift h hhR y hy))
      hGhL2 (lipschitzWith_diffQuot hu e h) (hDQeq h hh hhR)
    have hw2 : ∫ y in ball x₀ (2 * R), diffQuot u e h y ^ 2 ≤
        (Ku : ℝ) ^ 2 * volume.real (ball x₀ (2 * R)) := by
      have := norm_setIntegral_le_of_norm_le_const
        (measure_ball_lt_top (μ := volume) (x := x₀) (r := 2 * R))
        (f := fun y ↦ diffQuot u e h y ^ 2) (C := (Ku : ℝ) ^ 2) (fun y _ ↦ by
          rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
          have h1 := abs_diffQuot_le hu e hh y
          have h2 : (Ku : ℝ) * ‖e‖ ≤ Ku := mul_le_of_le_one_right Ku.2 he
          exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)] at this
      exact this
    have hG2 : ∫ y in ball x₀ (2 * R), ‖Gh h y‖ ^ 2 ≤
        (CG + Ca * Ku) ^ 2 * volume.real (ball x₀ (2 * R)) := by
      have := norm_setIntegral_le_of_norm_le_const
        (measure_ball_lt_top (μ := volume) (x := x₀) (r := 2 * R))
        (f := fun y ↦ ‖Gh h y‖ ^ 2) (C := (CG + Ca * Ku) ^ 2) (fun y hy ↦ by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hGh_bd h hh hhR y hy) 2)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)] at this
      exact this
    simp only [norm_gradient_eq_norm_fderiv] at hcac
    refine hcac.trans ?_
    rw [hEdef]
    gcongr
  have hu' : ∀ y ∈ ball x₀ R, DifferentiableAt ℝ u y := fun y hy ↦ hu_diff y (hW (hRW hy))
  obtain ⟨ρ, hρ, -, M, hM0, hdM, hholM⟩ := holder_partial_of_diffQuot hd hγ0 hγ1 hν hνΛ hR hHa
    e hu' hR (by positivity : 0 ≤ HdG + Hda * Ku + Ca * Hu) hE0 (fun h y ↦ a (y + h • e)) Gh
    (fun h _ hhR y hy v w ↦ hsymm _ (hshift h hhR y (hRW hy)) v w)
    (fun h _ hhR y hy ξ ↦ hell _ (hshift h hhR y (hRW hy)) ξ)
    (fun h _ hhR y hy ↦ hbd _ (hshift h hhR y (hRW hy)))
    (fun h _ hhR y hy y' hy' ↦ by
      have := ha_hol _ (hshift h hhR y (hRW hy)) _ (hshift h hhR y' (hRW hy'))
      rwa [dist_add_right] at this)
    hGh_hol (fun h _ ↦ ⟨_, lipschitzWith_diffQuot hu e h⟩)
    (fun h hh hhR ↦ (hDQeq h hh hhR).mono hRW) hE
  exact ⟨ρ, hρ, M, hM0, hdM, hholM⟩

/-! ### Differentiating weak equations -/

/-- The second derivative of a `C²` function, applied in either order. -/
theorem fderiv_fderiv_apply_comm {f : Space d → ℝ} {y : Space d} (hf : ContDiffAt ℝ 2 f y)
    (v w : Space d) :
    fderiv ℝ (fun z ↦ fderiv ℝ f z v) y w = fderiv ℝ (fun z ↦ fderiv ℝ f z w) y v := by
  have hd2 : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : ∀ u : Space d, fderiv ℝ (fun z ↦ fderiv ℝ f z u) y = (fderiv ℝ (fderiv ℝ f) y).flip u := by
    intro u
    have := (hd2.hasFDerivAt.clm_apply (hasFDerivAt_const u y))
    rw [this.fderiv]
    ext x
    simp
  rw [h1, h1, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact (hf.isSymmSndFDerivAt (by simp)) w v

theorem differentiableAt_gradient_of_contDiffAt' {f : Space d → ℝ} {y : Space d}
    (hf : ContDiffAt ℝ 2 f y) : DifferentiableAt ℝ (gradient f) y := by
  have h1 : ContDiffAt ℝ 1 (fun x ↦ (toDual ℝ (Space d)).symm (fderiv ℝ f x)) y :=
    (toDual ℝ (Space d)).symm.contDiff.contDiffAt.comp y (hf.fderiv_right (m := 1) (by norm_num))
  exact h1.differentiableAt (by simp)

/-- `∂_e ∇f = ∇ ∂_e f` for `C²` functions. -/
theorem fderiv_gradient_apply {f : Space d → ℝ} {y : Space d} (hf : ContDiffAt ℝ 2 f y)
    (e : Space d) : fderiv ℝ (gradient f) y e = gradient (fun z ↦ fderiv ℝ f z e) y := by
  have hgd := differentiableAt_gradient_of_contDiffAt' hf
  apply ext_inner_left ℝ
  intro w
  have h1 : inner ℝ w (fderiv ℝ (gradient f) y e) =
      fderiv ℝ (fun z ↦ fderiv ℝ f z w) y e := by
    have hcomp := ((innerSL ℝ w).hasFDerivAt.comp y hgd.hasFDerivAt).fderiv
    have hfun : (fun z ↦ fderiv ℝ f z w) = fun z ↦ innerSL ℝ w (gradient f z) := by
      funext z
      rw [innerSL_apply_apply, inner_gradient_right, conj_trivial]
    rw [hfun]
    change _ = fderiv ℝ ((innerSL ℝ w) ∘ gradient f) y e
    rw [hcomp]
    rfl
  rw [h1, inner_gradient_right, conj_trivial]
  exact fderiv_fderiv_apply_comm hf w e

/-- **Differentiating a weakly divergence-free `C¹` field**: its directional derivatives are
again weakly divergence free. -/
theorem IsWeakDivFree.fderiv_apply {U : Set (Space d)} (hU : IsOpen U) {V : Space d → Space d}
    (hV : ContDiffOn ℝ 1 V U) (hdiv : IsWeakDivFree V U) (e : Space d) :
    IsWeakDivFree (fun y ↦ fderiv ℝ V y e) U := by
  refine IsWeakDivFree.of_smooth hU (((hV.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply
    continuousOn_const).locallyIntegrableOn hU.measurableSet) (fun ψ hψ hψc hψU ↦ ?_)
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hψd : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ2.fderiv_right (m := 1) (by norm_num)
  have hVj1 : ∀ j, ContDiffOn ℝ 1 (fun z ↦ inner ℝ (b j) (V z)) U := fun j ↦
    (innerSL ℝ (b j)).contDiff.comp_contDiffOn hV
  have hψj1 : ∀ j, ContDiff ℝ 1 (fun z ↦ fderiv ℝ ψ z (b j)) := fun j ↦
    hψd.clm_apply contDiff_const
  have hψjc : ∀ j, HasCompactSupport (fun z ↦ fderiv ℝ ψ z (b j)) := fun j ↦
    hψc.fderiv_apply ℝ _
  have hψjU : ∀ j, tsupport (fun z ↦ fderiv ℝ ψ z (b j)) ⊆ U := fun j ↦
    (tsupport_fderiv_apply_subset ℝ _).trans hψU
  -- the test `∂_e ψ`
  have hχ1 : ContDiff ℝ 1 (fun z ↦ fderiv ℝ ψ z e) := hψd.clm_apply contDiff_const
  have hχc : HasCompactSupport (fun z ↦ fderiv ℝ ψ z e) := hψc.fderiv_apply ℝ _
  have hχU : tsupport (fun z ↦ fderiv ℝ ψ z e) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ _).trans hψU
  obtain ⟨Kχ, hKχ⟩ := hχ1.lipschitzWith_of_hasCompactSupport hχc one_ne_zero
  have h0 := hdiv _ ⟨Kχ, hKχ⟩ hχc hχU
  -- pointwise expansions
  have hexp1 : ∀ y, inner ℝ (V y) (gradient (fun z ↦ fderiv ℝ ψ z e) y) =
      ∑ j, inner ℝ (b j) (V y) * fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b j)) y e := by
    intro y
    rw [← b.sum_inner_mul_inner (V y) (gradient (fun z ↦ fderiv ℝ ψ z e) y)]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [real_inner_comm (V y) (b j)]
    congr 1
    rw [inner_gradient_right, conj_trivial]
    exact fderiv_fderiv_apply_comm hψ2.contDiffAt e (b j)
  have hexp2 : ∀ y ∈ U, inner ℝ (fderiv ℝ V y e) (gradient ψ y) =
      ∑ j, fderiv ℝ (fun z ↦ inner ℝ (b j) (V z)) y e * fderiv ℝ ψ y (b j) := by
    intro y hy
    have hVd : DifferentiableAt ℝ V y :=
      (hV.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
    rw [← b.sum_inner_mul_inner (fderiv ℝ V y e) (gradient ψ y)]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    have h1 : fderiv ℝ (fun z ↦ inner ℝ (b j) (V z)) y e = inner ℝ (b j) (fderiv ℝ V y e) := by
      have := ((innerSL ℝ (b j)).hasFDerivAt.comp y hVd.hasFDerivAt).fderiv
      change fderiv ℝ ((innerSL ℝ (b j)) ∘ V) y e = _
      rw [this]
      rfl
    rw [h1, real_inner_comm (b j) (fderiv ℝ V y e), inner_gradient_right, conj_trivial]
  -- integration by parts in each coordinate
  have hibp : ∀ j, ∫ y, inner ℝ (b j) (V y) * fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b j)) y e =
      -∫ y, fderiv ℝ (fun z ↦ inner ℝ (b j) (V z)) y e * fderiv ℝ ψ y (b j) := fun j ↦
    integral_mul_fderiv_eq_neg_of_hasCompactSupport hU (hVj1 j) (hψj1 j) (hψjc j) (hψjU j) e
  have hint1 : ∀ j, Integrable (fun y ↦ inner ℝ (b j) (V y) *
      fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b j)) y e) := by
    intro j
    have hc : Continuous (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b j)) y e) :=
      ((hψj1 j).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b j)) y e) :=
      (hψjc j).fderiv_apply ℝ _
    have hsub : tsupport (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b j)) y e) ⊆ U :=
      (tsupport_fderiv_apply_subset ℝ _).trans (hψjU j)
    refine ((((hVj1 j).continuousOn.mono hsub).mul hc.continuousOn).integrableOn_compact
      hsupp.isCompact).integrable_of_forall_notMem_eq_zero (fun y hy ↦ ?_)
    have h0 : fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b j)) y e = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b j)) y e) hy
    show inner ℝ (b j) (V y) * fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b j)) y e = 0
    rw [h0, mul_zero]
  have hint2 : ∀ j, Integrable (fun y ↦ fderiv ℝ (fun z ↦ inner ℝ (b j) (V z)) y e *
      fderiv ℝ ψ y (b j)) := by
    intro j
    have hc : ContinuousOn (fun y ↦ fderiv ℝ (fun z ↦ inner ℝ (b j) (V z)) y e) U :=
      ((hVj1 j).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    refine ((hc.mono (hψjU j)).mul (hψj1 j).continuous.continuousOn |>.integrableOn_compact
      (hψjc j).isCompact).integrable_of_forall_notMem_eq_zero (fun y hy ↦ ?_)
    have h0 : fderiv ℝ ψ y (b j) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun z ↦ fderiv ℝ ψ z (b j)) hy
    show fderiv ℝ (fun z ↦ inner ℝ (b j) (V z)) y e * fderiv ℝ ψ y (b j) = 0
    rw [h0, mul_zero]
  have hsum1 : ∫ y, inner ℝ (V y) (gradient (fun z ↦ fderiv ℝ ψ z e) y) =
      ∑ j, ∫ y, inner ℝ (b j) (V y) * fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b j)) y e := by
    simp_rw [hexp1]
    exact integral_finsetSum _ (fun j _ ↦ hint1 j)
  have hgψ0 : ∀ y, y ∉ U → gradient ψ y = 0 := fun y hy ↦
    gradient_eq_zero_of_notMem_tsupport (fun h ↦ hy (hψU h))
  have hsum2 : ∫ y, inner ℝ (fderiv ℝ V y e) (gradient ψ y) =
      ∑ j, ∫ y, fderiv ℝ (fun z ↦ inner ℝ (b j) (V z)) y e * fderiv ℝ ψ y (b j) := by
    rw [← integral_finsetSum _ (fun j _ ↦ hint2 j)]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ U
    · exact hexp2 y hy
    · have hψ0 : ∀ j, fderiv ℝ ψ y (b j) = 0 := fun j ↦ by
        rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hψU h))]
        rfl
      simp [hgψ0 y hy, hψ0]
  rw [hsum2]
  rw [hsum1] at h0
  simp_rw [hibp] at h0
  rw [Finset.sum_neg_distrib, neg_eq_zero] at h0
  exact h0

/-! ### The linear bootstrap -/

theorem holderC_one_of_local {U : Set (Space d)} {g : Space d → ℝ} {β : ℝ}
    (h : ∀ x ∈ U, ∃ ρ > 0, ball x ρ ⊆ U ∧ ∃ M,
      (∀ y ∈ ball x ρ, DifferentiableAt ℝ g y) ∧
      ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖fderiv ℝ g y - fderiv ℝ g z‖ ≤ M * dist y z ^ β) :
    HolderC β U 1 g := by
  refine ⟨fun y hy ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨ρ, hρ, -, -, hdM, -⟩ := h y hy
    exact (hdM y (mem_ball_self hρ)).differentiableWithinAt
  · obtain ⟨ρ, hρ, hρU, M, -, hholM⟩ := h x hx
    exact ⟨ρ, hρ, hρU, M, hholM⟩

/-- Local data for a `C^{1,γ}` function near a point: a ball on which it is Lipschitz-extended,
differentiable, with `γ`-Hölder derivative. -/
theorem exists_ball_holder_of_holderC {U : Set (Space d)} (hU : IsOpen U) {γ : ℝ}
    (_hγ0 : 0 < γ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space d → F}
    (hf : HolderC γ U 1 f) {x : Space d} (hx : x ∈ U) :
    ∃ r > 0, ball x r ⊆ U ∧ ∃ H, 0 ≤ H ∧ (∀ y ∈ ball x r, DifferentiableAt ℝ f y) ∧
      ∀ y ∈ ball x r, ∀ z ∈ ball x r, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ H * dist y z ^ γ := by
  obtain ⟨r, hr, hrU, M, hM⟩ := hf.2 x hx
  refine ⟨r, hr, hrU, max M 0, le_max_right _ _, fun y hy ↦ (hf.1 y (hrU hy)).differentiableAt
    (hU.mem_nhds (hrU hy)), fun y hy z hz ↦ (hM y hy z hz).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))⟩

/-- **`C^{2}` regularity for linear equations with `C^{1,γ}` data.** -/
theorem holderC_two_of_weakDivFree (hd : 0 < d) {U : Set (Space d)} (hU : IsOpen U)
    {a : Space d → Space d →L[ℝ] Space d} {G : Space d → Space d} {u : Space d → ℝ}
    {ν Λ γ : ℝ} (hν : 0 < ν) (hνΛ : ν ≤ Λ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hsymm : ∀ y ∈ U, ∀ v w, inner ℝ (a y v) w = inner ℝ v (a y w))
    (hell : ∀ y ∈ U, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a y ξ) ξ) (hbd : ∀ y ∈ U, ‖a y‖ ≤ Λ)
    (ha : HolderC γ U 1 a) (hG : HolderC γ U 1 G) (hu : ContDiffOn ℝ 1 u U)
    (heq : IsWeakDivFree (fun y ↦ a y (gradient u y) - G y) U) :
    HolderC (γ / 4 / 4) U 2 u := by
  have ha0 : LocHolderOn γ a U := HolderC.of_succ hγ0 hγ1 hU ha
  have hG0 : LocHolderOn γ G U := HolderC.of_succ hγ0 hγ1 hU hG
  have hu1 : HolderC (γ / 4) U 1 u :=
    holderC_one_of_weakDivFree hd hν hνΛ hγ0 hγ1 hsymm hell hbd ha0 hG0 hu heq
  set γ₁ := γ / 4 with hγ₁
  have hγ₁0 : 0 < γ₁ := by positivity
  have hγ₁1 : γ₁ ≤ 1 := by linarith
  have hγ₁γ : γ₁ ≤ γ := by linarith
  have ha1 : HolderC γ₁ U 1 a := HolderC.mono_exp hγ₁0 hγ₁γ ha
  have hG1 : HolderC γ₁ U 1 G := HolderC.mono_exp hγ₁0 hγ₁γ hG
  have ha01 : LocHolderOn γ₁ a U := LocHolderOn.mono_exp hγ₁0 hγ₁γ ha0
  refine holderC_succ_of_partials hU hu1.1 (fun i ↦ holderC_one_of_local (fun x hx ↦ ?_))
  set v : Space d := EuclideanSpace.single i 1 with hv
  have hv1 : ‖v‖ ≤ 1 := by rw [hv]; simp
  obtain ⟨r₁, hr₁, hr₁U, Hda, hHda, hda_diff, hda_hol⟩ :=
    exists_ball_holder_of_holderC hU hγ₁0 ha1 hx
  obtain ⟨r₂, hr₂, -, HdG, hHdG, hdG_diff, hdG_hol⟩ :=
    exists_ball_holder_of_holderC hU hγ₁0 hG1 hx
  obtain ⟨r₃, hr₃, -, Hu, hHu, hu_diff, hu_hol⟩ := exists_ball_holder_of_holderC hU hγ₁0 hu1 hx
  obtain ⟨r₄, hr₄, -, Ha, ha_hol⟩ := ha01 x hx
  set R₀ := min (min r₁ r₂) (min r₃ r₄) / 2 with hR₀
  have hR₀0 : 0 < R₀ := by positivity
  have hmin : min (min r₁ r₂) (min r₃ r₄) ≤ r₁ ∧ min (min r₁ r₂) (min r₃ r₄) ≤ r₂ ∧
      min (min r₁ r₂) (min r₃ r₄) ≤ r₃ ∧ min (min r₁ r₂) (min r₃ r₄) ≤ r₄ :=
    ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hmpos : 0 < min (min r₁ r₂) (min r₃ r₄) := by positivity
  have hs₁ : closedBall x R₀ ⊆ ball x r₁ := closedBall_subset_ball (by linarith [hmin.1])
  have hs₂ : ball x R₀ ⊆ ball x r₂ := ball_subset_ball (by linarith [hmin.2.1])
  have hs₃ : ball x R₀ ⊆ ball x r₃ := ball_subset_ball (by linarith [hmin.2.2.1])
  have hs₄ : ball x R₀ ⊆ ball x r₄ := ball_subset_ball (by linarith [hmin.2.2.2])
  have hs₁' : ball x R₀ ⊆ ball x r₁ := ball_subset_closedBall.trans hs₁
  have hxR : closedBall x R₀ ⊆ U := hs₁.trans hr₁U
  -- derivative bounds
  have hDa_c := LocHolderOn.continuousOn hγ₁0 ha1.2
  have hDG_c := LocHolderOn.continuousOn hγ₁0 hG1.2
  obtain ⟨Ca, hCa⟩ := (isCompact_closedBall x R₀).exists_bound_of_continuousOn (hDa_c.mono hxR)
  obtain ⟨CG, hCG⟩ := (isCompact_closedBall x R₀).exists_bound_of_continuousOn (hDG_c.mono hxR)
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (hCa x (mem_closedBall_self hR₀0.le))
  have hCG0 : 0 ≤ CG := (norm_nonneg _).trans (hCG x (mem_closedBall_self hR₀0.le))
  -- the Lipschitz extension of `u`
  obtain ⟨Ku, ũ, hũ, hũeq⟩ := exists_lipschitz_eqOn_closedBall hu hxR
  have hev : ∀ y ∈ ball x R₀, u =ᶠ[𝓝 y] ũ := fun y hy ↦ by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact hũeq (ball_subset_closedBall hz)
  have hBU : ball x R₀ ⊆ U := ball_subset_closedBall.trans hxR
  obtain ⟨ρ, hρ, M, -, hdM, hholM⟩ := linear_partial_holder_ball hd hũ hR₀0 (Ha := max Ha 0)
    (Hda := Hda) (HdG := HdG) (Hu := Hu) (Ca := Ca) (CG := CG) hν hνΛ hγ₁0 hγ₁1
    (le_max_right _ _) hHda hHdG hHu hCa0 hCG0
    (fun y hy ↦ hsymm y (hBU hy)) (fun y hy ↦ hell y (hBU hy)) (fun y hy ↦ hbd y (hBU hy))
    (fun y hy ↦ hda_diff y (hs₁' hy)) (fun y hy ↦ hdG_diff y (hs₂ hy))
    (fun y hy z hz ↦ (ha_hol y (hs₄ hy) z (hs₄ hz)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)))
    (fun y hy z hz ↦ hda_hol y (hs₁' hy) z (hs₁' hz))
    (fun y hy z hz ↦ hdG_hol y (hs₂ hy) z (hs₂ hz))
    (fun y hy ↦ hCa y (ball_subset_closedBall hy)) (fun y hy ↦ hCG y (ball_subset_closedBall hy))
    (fun y hy ↦ ((hev y hy).differentiableAt_iff).1 (hu_diff y (hs₃ hy)))
    (fun y hy z hz ↦ by
      rw [← fderiv_eq_of_eqOn_ball hũeq hy, ← fderiv_eq_of_eqOn_ball hũeq hz]
      exact hu_hol y (hs₃ hy) z (hs₃ hz))
    ((heq.mono hBU).congr_ae (Eventually.of_forall fun y hy ↦ by
      rw [gradient_eq_of_eqOn_ball hũeq hy])) hv1
  have hev' : ∀ y ∈ ball x R₀, (fun z ↦ fderiv ℝ u z v) =ᶠ[𝓝 y]
      (fun z ↦ fderiv ℝ ũ z v) := fun y hy ↦ by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    rw [fderiv_eq_of_eqOn_ball hũeq hz]
  refine ⟨min ρ R₀, lt_min hρ hR₀0, (ball_subset_ball (min_le_right _ _)).trans hBU, M,
    fun y hy ↦ ?_, fun y hy z hz ↦ ?_⟩
  · have hy₂ := ball_subset_ball (min_le_right _ _) hy
    exact ((hev' y hy₂).differentiableAt_iff).2 (hdM y (ball_subset_ball (min_le_left _ _) hy))
  · have hy₂ := ball_subset_ball (min_le_right _ _) hy
    have hz₂ := ball_subset_ball (min_le_right _ _) hz
    rw [(hev' y hy₂).fderiv_eq, (hev' z hz₂).fderiv_eq]
    exact hholM y (ball_subset_ball (min_le_left _ _) hy) z (ball_subset_ball (min_le_left _ _) hz)

/-- **Linear regularity at order `k`**: `C^{k,γ}` coefficients and right-hand side give
`C^{k+1,γ'}` solutions, for an exponent `γ'` depending only on `γ`. -/
def LinearRegularity (d k : ℕ) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∃ γ' : ℝ, 0 < γ' ∧ γ' ≤ 1 ∧
    ∀ (U : Set (Space d)) (ν Λ : ℝ) (a : Space d → Space d →L[ℝ] Space d)
      (G : Space d → Space d) (u : Space d → ℝ),
      IsOpen U → 0 < ν → ν ≤ Λ →
      (∀ y ∈ U, ∀ v w, inner ℝ (a y v) w = inner ℝ v (a y w)) →
      (∀ y ∈ U, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a y ξ) ξ) → (∀ y ∈ U, ‖a y‖ ≤ Λ) →
      HolderC γ U k a → HolderC γ U k G → ContDiffOn ℝ 1 u U →
      IsWeakDivFree (fun y ↦ a y (gradient u y) - G y) U → HolderC γ' U (k + 1) u

theorem linearRegularity_zero (hd : 0 < d) : LinearRegularity d 0 := fun γ hγ0 hγ1 ↦
  ⟨γ / 4, by positivity, by linarith, fun _ _ _ _ _ _ _ hν hνΛ hsymm hell hbd ha hG hu heq ↦
    holderC_one_of_weakDivFree hd hν hνΛ hγ0 hγ1 hsymm hell hbd ha hG hu heq⟩

theorem linearRegularity_one (hd : 0 < d) : LinearRegularity d 1 := fun γ hγ0 hγ1 ↦
  ⟨γ / 4 / 4, by positivity, by linarith, fun _ _ _ _ _ _ hU hν hνΛ hsymm hell hbd ha hG hu heq ↦
    holderC_two_of_weakDivFree hd hU hν hνΛ hγ0 hγ1 hsymm hell hbd ha hG hu heq⟩

theorem holderC_gradient {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {U : Set (Space d)} (hU : IsOpen U)
    {k : ℕ} {u : Space d → ℝ} (hu : HolderC γ U (k + 1) u) :
    HolderC γ U k (gradient u) := by
  have h := HolderC.comp_contDiff (f := fderiv ℝ u) (Φ := fun L ↦ (toDual ℝ (Space d)).symm L)
    hγ0 hγ1 hU (toDual ℝ (Space d)).symm.contDiff hu.2
  exact HolderC.congr hU h (fun y _ ↦ rfl)

theorem linearRegularity_succ_succ {k : ℕ} (hk : LinearRegularity d (k + 1)) :
    LinearRegularity d (k + 2) := by
  intro γ hγ0 hγ1
  obtain ⟨γ₁, hγ₁0, hγ₁1, h₁⟩ := hk γ hγ0 hγ1
  have hγ₂0 : 0 < min γ γ₁ := lt_min hγ0 hγ₁0
  have hγ₂1 : min γ γ₁ ≤ 1 := (min_le_left _ _).trans hγ1
  obtain ⟨γ₃, hγ₃0, hγ₃1, h₃⟩ := hk (min γ γ₁) hγ₂0 hγ₂1
  refine ⟨γ₃, hγ₃0, hγ₃1, fun U ν Λ a G u hU hν hνΛ hsymm hell hbd ha hG hu heq ↦ ?_⟩
  have hu1 : HolderC γ₁ U (k + 2) u := h₁ U ν Λ a G u hU hν hνΛ hsymm hell hbd
    (HolderC.of_succ hγ0 hγ1 hU ha) (HolderC.of_succ hγ0 hγ1 hU hG) hu heq
  refine holderC_succ_of_partials hU hu1.1 (fun i ↦ ?_)
  set e : Space d := EuclideanSpace.single i 1 with he
  -- the data of the differentiated equation
  have ha' : HolderC (min γ γ₁) U (k + 1) a :=
    HolderC.mono_exp hγ₂0 (min_le_left _ _) (HolderC.of_succ hγ0 hγ1 hU ha)
  have hgu : HolderC γ₁ U (k + 1) (gradient u) := holderC_gradient hγ₁0 hγ₁1 hU hu1
  have hdG : HolderC γ U (k + 1) (fun y ↦ fderiv ℝ G y e) := HolderC.fderiv_apply hU hG e
  have hda : HolderC γ U (k + 1) (fun y ↦ fderiv ℝ a y e) := HolderC.fderiv_apply hU ha e
  have hprod : HolderC (min γ γ₁) U (k + 1) (fun y ↦ (fderiv ℝ a y e) (gradient u y)) :=
    HolderC.bilinear hγ₂0 hγ₂1 hU (ContinuousLinearMap.id ℝ (Space d →L[ℝ] Space d))
      (HolderC.mono_exp hγ₂0 (min_le_left _ _) hda)
      (HolderC.mono_exp hγ₂0 (min_le_right _ _) hgu)
  have hG' : HolderC (min γ γ₁) U (k + 1)
      (fun y ↦ fderiv ℝ G y e - (fderiv ℝ a y e) (gradient u y)) :=
    HolderC.sub hU (HolderC.mono_exp hγ₂0 (min_le_left _ _) hdG) hprod
  have hv1 : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y e) U := by
    have := HolderC.contDiffOn hγ₁0 hU (HolderC.fderiv_apply hU hu1 e)
    exact this.of_le (by norm_cast; omega)
  -- the differentiated equation
  have hu2 : ContDiffOn ℝ 2 u U := by
    have := HolderC.contDiffOn hγ₁0 hU hu1
    exact this.of_le (by norm_cast; omega)
  have ha1 : ContDiffOn ℝ 1 a U :=
    (HolderC.contDiffOn hγ0 hU ha).of_le (by norm_cast; omega)
  have hG1 : ContDiffOn ℝ 1 G U :=
    (HolderC.contDiffOn hγ0 hU hG).of_le (by norm_cast; omega)
  have hgu1 : ContDiffOn ℝ 1 (gradient u) U :=
    (HolderC.contDiffOn hγ₁0 hU hgu).of_le (by norm_cast; omega)
  have hV : ContDiffOn ℝ 1 (fun y ↦ a y (gradient u y) - G y) U :=
    (ha1.clm_apply hgu1).sub hG1
  have hdiv := IsWeakDivFree.fderiv_apply hU hV heq e
  have heq' : IsWeakDivFree (fun y ↦ a y (gradient (fun z ↦ fderiv ℝ u z e) y) -
      (fderiv ℝ G y e - (fderiv ℝ a y e) (gradient u y))) U := by
    refine hdiv.congr_ae (Eventually.of_forall fun y hy ↦ ?_)
    have hay : DifferentiableAt ℝ a y :=
      (ha1.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
    have hgy : DifferentiableAt ℝ (gradient u) y :=
      (hgu1.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
    have hGy : DifferentiableAt ℝ G y :=
      (hG1.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
    have h2 : ContDiffAt ℝ 2 u y := (hu2 y hy).contDiffAt (hU.mem_nhds hy)
    have hd1 : fderiv ℝ (fun y ↦ a y (gradient u y)) y e =
        (fderiv ℝ a y e) (gradient u y) + a y (fderiv ℝ (gradient u) y e) := by
      rw [fderiv_clm_apply hay hgy]
      simp [add_comm]
    rw [fderiv_fun_sub (hay.clm_apply hgy) hGy, sub_apply, hd1,
      fderiv_gradient_apply h2 e]
    abel
  exact h₃ U ν Λ a _ _ hU hν hνΛ hsymm hell hbd ha' hG' hv1 heq'

theorem linearRegularity (hd : 0 < d) (k : ℕ) : LinearRegularity d k := by
  have h : ∀ k, LinearRegularity d (k + 1) := by
    intro k
    induction k with
    | zero => exact linearRegularity_one hd
    | succ k ih => exact linearRegularity_succ_succ ih
  cases k with
  | zero => exact linearRegularity_zero hd
  | succ k => exact h k

end SerrinEpigraph
