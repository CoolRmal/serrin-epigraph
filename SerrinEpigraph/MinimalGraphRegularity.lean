module

public import SerrinEpigraph.SchauderBootstrap

/-!
# Smoothness of `C¹` weak solutions of the minimal surface equation

For the flux `A(p) = p / √(1 + |p|²)` (`minimalSurfaceFlux`) and an open set `U ⊆ ℝ^d`:

* `holderC_one_of_minimalSurface`: a `C¹` weak solution of `div A(∇φ) = 0` on `U` is
  `C^{1,1/2}` (nonlinear Campanato iteration: comparison with the linearization `DA(b)` at the mean
  gradient, whose error is quadratic in the oscillation of `∇φ`; `minimalSurface_fderiv_holder_ball`);
* `holderC_two_of_minimalSurface`: `C^{1,γ}` weak solutions are `C^{2,γ/4}` (uniform Schauder
  estimates for the difference quotients, which solve `div (A_h ∇w) = 0` with the averaged
  coefficients `A_h = ∫₀¹ DA(...)`, and passage to the limit);
* `minimalSurface_holderC_succ_succ`: the bootstrap `C^{m+2,γ} → C^{m+3,γ'}`, from the linearized
  equation `div (DA(∇φ) ∇∂ₑφ) = 0` and the linear regularity `linearRegularity`;
* `contDiffOn_infty_of_weak_minimalSurface`: **`C¹` weak solutions are `C^∞` on `U`**, and
  `minimalSurface_contDiffOn_top_proof`, the same statement on a ball in the form used by
  `RigidityReduction.minimalSurface_contDiffOn_top`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff

namespace SerrinEpigraph

variable {d : ℕ}

/-! ### The minimal surface flux -/

theorem contDiff_minimalSurfaceFlux_infty : ContDiff ℝ ∞ (minimalSurfaceFlux (d := d)) := by
  have h1 : ContDiff ℝ ∞ (fun q : Space d ↦ 1 + ‖q‖ ^ 2) :=
    contDiff_const.add (contDiff_norm_sq ℝ)
  have h2 : ContDiff ℝ ∞ (fun q : Space d ↦ Real.sqrt (1 + ‖q‖ ^ 2)) :=
    h1.sqrt (fun q ↦ (by positivity : (0 : ℝ) < 1 + ‖q‖ ^ 2).ne')
  have h3 : ContDiff ℝ ∞ (fun q : Space d ↦ (Real.sqrt (1 + ‖q‖ ^ 2))⁻¹) :=
    h2.inv (fun q ↦ (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + ‖q‖ ^ 2)).ne')
  exact h3.smul contDiff_id

theorem inner_fderiv_minimalSurfaceFlux_comm (p ξ η : Space d) :
    inner ℝ (fderiv ℝ minimalSurfaceFlux p ξ) η = inner ℝ ξ (fderiv ℝ minimalSurfaceFlux p η) := by
  rw [fderiv_minimalSurfaceFlux_apply, fderiv_minimalSurfaceFlux_apply, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_right, real_inner_comm p ξ]
  ring

/-- The derivative of the flux is Lipschitz on every closed ball. -/
theorem exists_lipschitzOnWith_fderiv_minimalSurfaceFlux (L : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ (minimalSurfaceFlux (d := d)))
      (closedBall 0 L) := by
  have h : ContDiff ℝ 1 (fderiv ℝ (minimalSurfaceFlux (d := d))) :=
    (contDiff_minimalSurfaceFlux_infty.fderiv_right (m := 1) (by simp))
  exact h.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 L)
    (isCompact_closedBall 0 L)

private theorem mem_closedBall_segment_aux {L : ℝ} {p q : Space d} (hp : ‖p‖ ≤ L) (hq : ‖q‖ ≤ L)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : p + t • (q - p) ∈ closedBall (0 : Space d) L := by
  have hp' : p ∈ closedBall (0 : Space d) L := by simpa using hp
  have hq' : q ∈ closedBall (0 : Space d) L := by simpa using hq
  have h := (convex_closedBall (0 : Space d) L) hp' hq' (sub_nonneg.2 ht.2) ht.1
    (by ring : (1 - t) + t = 1)
  have e : (1 - t) • p + t • q = p + t • (q - p) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rwa [e] at h

/-- **Quadratic Taylor bound** for the flux on the ball `‖p‖ ≤ L`. -/
theorem norm_minimalSurfaceFlux_taylor_le {L : ℝ} {K : NNReal}
    (hK : LipschitzOnWith K (fderiv ℝ (minimalSurfaceFlux (d := d))) (closedBall 0 L))
    {p q : Space d} (hp : ‖p‖ ≤ L) (hq : ‖q‖ ≤ L) :
    ‖minimalSurfaceFlux q - minimalSurfaceFlux p - fderiv ℝ minimalSurfaceFlux p (q - p)‖ ≤
      K * ‖q - p‖ ^ 2 := by
  set s := closedBall (0 : Space d) L ∩ closedBall p ‖q - p‖ with hs
  have hsc : Convex ℝ s := (convex_closedBall _ _).inter (convex_closedBall _ _)
  have hp0 : p ∈ closedBall (0 : Space d) L := by simpa using hp
  have hq0 : q ∈ closedBall (0 : Space d) L := by simpa using hq
  have hps : p ∈ s := ⟨hp0, mem_closedBall_self (norm_nonneg _)⟩
  have hqs : q ∈ s := ⟨hq0, by rw [mem_closedBall, dist_eq_norm]⟩
  have hdiff : Differentiable ℝ (minimalSurfaceFlux (d := d)) :=
    contDiff_minimalSurfaceFlux.differentiable one_ne_zero
  have hgd : ∀ z ∈ s, DifferentiableAt ℝ
      (fun z ↦ minimalSurfaceFlux z - fderiv ℝ minimalSurfaceFlux p z) z := fun z _ ↦
    (hdiff z).sub (fderiv ℝ minimalSurfaceFlux p).differentiableAt
  have hbd : ∀ z ∈ s, ‖fderiv ℝ (fun z ↦ minimalSurfaceFlux z -
      fderiv ℝ minimalSurfaceFlux p z) z‖ ≤ K * ‖q - p‖ := by
    intro z hz
    rw [fderiv_fun_sub (hdiff z) (fderiv ℝ minimalSurfaceFlux p).differentiableAt,
      ContinuousLinearMap.fderiv]
    have h1 := hK.dist_le_mul z hz.1 p hp0
    rw [dist_eq_norm, dist_eq_norm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hz.2) K.2)
  have h := hsc.norm_image_sub_le_of_norm_fderiv_le hgd hbd hps hqs
  calc ‖minimalSurfaceFlux q - minimalSurfaceFlux p - fderiv ℝ minimalSurfaceFlux p (q - p)‖ =
      ‖(minimalSurfaceFlux q - fderiv ℝ minimalSurfaceFlux p q) -
        (minimalSurfaceFlux p - fderiv ℝ minimalSurfaceFlux p p)‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ K * ‖q - p‖ * ‖q - p‖ := h
    _ = K * ‖q - p‖ ^ 2 := by ring

theorem norm_minimalSurfaceFlux_le (p : Space d) : ‖minimalSurfaceFlux p‖ ≤ ‖p‖ := by
  unfold minimalSurfaceFlux
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  have h1 : 1 ≤ Real.sqrt (1 + ‖p‖ ^ 2) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + ‖p‖ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖p‖])
  have h2 : (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  calc (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ * ‖p‖ ≤ 1 * ‖p‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖p‖ := one_mul _

/-- An average of values within `ε` of `v` is within `ε` of `v`. -/
theorem norm_setAverage_sub_le_of_forall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {S : Set (Space d)} (_hSm : MeasurableSet S) (hS0 : volume S ≠ 0)
    (hS : volume S ≠ ⊤) {f : Space d → E} (hf : IntegrableOn f S) {v : E} {ε : ℝ}
    (hε : ∀ y ∈ S, ‖f y - v‖ ≤ ε) : ‖(⨍ y in S, f y) - v‖ ≤ ε := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS
  have hm : 0 < volume.real S := ENNReal.toReal_pos hS0 hS
  have h1 : (⨍ y in S, f y) - v = (volume.real S)⁻¹ • ∫ y in S, (f y - v) := by
    rw [setAverage_eq, integral_sub hf (integrable_const v), setIntegral_const, smul_sub,
      smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
  rw [h1, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h2 : ‖∫ y in S, (f y - v)‖ ≤ ε * volume.real S := by
    have := norm_setIntegral_le_of_norm_le_const (hS.lt_top) (fun y hy ↦ hε y hy)
    simpa [Measure.real, mul_comm] using this
  calc (volume.real S)⁻¹ * ‖∫ y in S, (f y - v)‖ ≤ (volume.real S)⁻¹ * (ε * volume.real S) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ε := by field_simp

/-! ### `C¹` solutions are `C^{1,1/2}` -/

theorem isUniformlyElliptic_fderiv_minimalSurfaceFlux (hd : 0 < d) {L : ℝ} {b : Space d}
    (hb : ‖b‖ ≤ L) :
    IsUniformlyElliptic (fderiv ℝ minimalSurfaceFlux b) ((Real.sqrt (1 + L ^ 2) ^ 3)⁻¹) 2 :=
  isUniformlyElliptic_of_bounds hd (by positivity) (inner_fderiv_minimalSurfaceFlux_comm b)
    ((isEllipticFlux_minimalSurfaceFlux L).elliptic b hb) (norm_fderiv_minimalSurfaceFlux_le b)

/-- **One step of the nonlinear excess decay**: if `∇φ` oscillates by at most `ε` on `B_r(x)`,
the excess of `Dφ` improves by the factor `θ^(d+1)` from `B_r(x)` to `B_{θr}(x)`. -/
theorem minimalSurface_excess_decay_step (hd : 0 < d) {φ : Space d → ℝ} {Lφ : NNReal}
    (hφ : LipschitzWith Lφ φ) {KT : NNReal}
    (hKT : LipschitzOnWith KT (fderiv ℝ (minimalSurfaceFlux (d := d))) (closedBall 0 (Lφ : ℝ)))
    {x : Space d} {r : ℝ} (hr : 0 < r)
    (hdiv : IsWeakDivFree (fun y ↦ minimalSurfaceFlux (gradient φ y)) (ball x r))
    {ε : ℝ} (hclose : ∀ y ∈ ball x r, ‖fderiv ℝ φ y - fderiv ℝ φ x‖ ≤ ε)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ14 : θ ≤ 1 / 4)
    (hθC : excessDecayConst₁ d ((Real.sqrt (1 + (Lφ : ℝ) ^ 2) ^ 3)⁻¹) 2 * θ ≤ 1 / 2)
    (hε2 : excessDecayConst₂ d ((Real.sqrt (1 + (Lφ : ℝ) ^ 2) ^ 3)⁻¹) 2 *
      ((KT : ℝ) ^ 2 * (2 * ε) ^ 2) ≤ θ ^ (d + 1) / 2) :
    ∫ y in ball x (θ * r), ‖fderiv ℝ φ y - ⨍ z in ball x (θ * r), fderiv ℝ φ z‖ ^ 2 ≤
      θ ^ (d + 1) * ∫ y in ball x r, ‖fderiv ℝ φ y - ⨍ z in ball x r, fderiv ℝ φ z‖ ^ 2 := by
  set L : ℝ := (Lφ : ℝ) with hLdef
  have hL0 : 0 ≤ L := Lφ.2
  have hgradL : ∀ y, ‖gradient φ y‖ ≤ L := fun y ↦ by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hφ
  have hfin : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball x r)) := isFiniteMeasure_restrict.2 hfin
  have hpos : volume (ball x r) ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hDL2 := memLp_fderiv_of_lipschitz hφ _ hfin
  have hDint : IntegrableOn (fderiv ℝ φ) (ball x r) := hDL2.integrable one_le_two
  obtain ⟨c, hc⟩ : ∃ c, ⨍ z in ball x r, fderiv ℝ φ z = c := ⟨_, rfl⟩
  rw [hc]
  have hcx : ‖c - fderiv ℝ φ x‖ ≤ ε := by
    rw [← hc]
    exact norm_setAverage_sub_le_of_forall measurableSet_ball hpos hfin hDint hclose
  have hcL : ‖c‖ ≤ L := by
    have := norm_setAverage_sub_le_of_forall measurableSet_ball hpos hfin hDint (v := 0)
      (fun y _ ↦ by rw [sub_zero]; exact norm_fderiv_le_of_lipschitz ℝ hφ)
    rw [hc, sub_zero] at this
    exact this
  obtain ⟨b, hb⟩ : ∃ b, b = (toDual ℝ (Space d)).symm c := ⟨_, rfl⟩
  have hbL : ‖b‖ ≤ L := by rw [hb, LinearIsometryEquiv.norm_map]; exact hcL
  have hgb : ∀ y, ‖gradient φ y - b‖ = ‖fderiv ℝ φ y - c‖ := fun y ↦ by
    rw [gradient, hb, ← map_sub, LinearIsometryEquiv.norm_map]
  have hgb2 : ∀ y ∈ ball x r, ‖fderiv ℝ φ y - c‖ ≤ 2 * ε := by
    intro y hy
    have h1 := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ φ y) (fderiv ℝ φ x) c
    have h2 := hclose y hy
    have h3 : ‖fderiv ℝ φ x - c‖ ≤ ε := by rw [norm_sub_rev]; exact hcx
    linarith
  obtain ⟨A₀, hA₀⟩ : ∃ A, A = fderiv ℝ minimalSurfaceFlux b := ⟨_, rfl⟩
  obtain ⟨Rm, hRm⟩ : ∃ Rm : Space d → Space d, Rm = fun y ↦ minimalSurfaceFlux (gradient φ y) -
      minimalSurfaceFlux b - A₀ (gradient φ y - b) := ⟨_, rfl⟩
  have hRm_le : ∀ y ∈ ball x r, ‖Rm y‖ ≤ KT * (2 * ε) * ‖fderiv ℝ φ y - c‖ := by
    intro y hy
    have h1 := norm_minimalSurfaceFlux_taylor_le hKT hbL (hgradL y)
    have h2 := hgb2 y hy
    rw [hRm, hA₀]
    have h3 : (KT : ℝ) * ‖fderiv ℝ φ y - c‖ ^ 2 ≤ KT * (2 * ε) * ‖fderiv ℝ φ y - c‖ := by
      rw [sq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 KT.2) (norm_nonneg _)
    calc ‖minimalSurfaceFlux (gradient φ y) - minimalSurfaceFlux b -
          fderiv ℝ minimalSurfaceFlux b (gradient φ y - b)‖ ≤ KT * ‖gradient φ y - b‖ ^ 2 := h1
      _ = KT * ‖fderiv ℝ φ y - c‖ ^ 2 := by rw [hgb]
      _ ≤ KT * (2 * ε) * ‖fderiv ℝ φ y - c‖ := h3
  have hgm : Measurable (gradient φ) :=
    (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
  have hVL2 : MemLp (fun y ↦ minimalSurfaceFlux (gradient φ y)) 2
      (volume.restrict (ball x r)) :=
    MemLp.of_bound (contDiff_minimalSurfaceFlux.continuous.measurable.comp hgm
      |>.aestronglyMeasurable) L
      (Eventually.of_forall fun y ↦ (norm_minimalSurfaceFlux_le _).trans (hgradL y))
  have hRm_meas : AEStronglyMeasurable Rm (volume.restrict (ball x r)) := by
    rw [hRm]
    exact ((contDiff_minimalSurfaceFlux.continuous.measurable.comp hgm).sub measurable_const
      |>.sub (A₀.continuous.measurable.comp (hgm.sub measurable_const))).aestronglyMeasurable
  have hRmL2 : MemLp (fun y ↦ -Rm y) 2 (volume.restrict (ball x r)) := by
    refine MemLp.of_bound hRm_meas.neg (KT * (2 * ε) * (L + ‖c‖)) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rw [norm_neg]
    refine (hRm_le y hy).trans ?_
    have h1 : ‖fderiv ℝ φ y - c‖ ≤ L + ‖c‖ := by
      have h2 := norm_sub_le (fderiv ℝ φ y) c
      have h3 := norm_fderiv_le_of_lipschitz ℝ hφ (x₀ := y)
      linarith
    have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hclose x (mem_ball_self hr))
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have heq : IsWeakDivFree (fun y ↦ A₀ (gradient φ y) - -Rm y) (ball x r) := by
    have h1 := hdiv.sub_const hVL2 (minimalSurfaceFlux b - A₀ b)
    refine h1.congr_ae (Eventually.of_forall fun y _ ↦ ?_)
    rw [hRm]
    simp only [map_sub]
    abel
  have hA₀ell := isUniformlyElliptic_fderiv_minimalSurfaceFlux hd (L := L) hbL
  rw [← hA₀] at hA₀ell
  have hA₀bd : ‖A₀‖ ≤ 2 := by rw [hA₀]; exact norm_fderiv_minimalSurfaceFlux_le b
  have hdec := excess_decay_of_weakDivFree hd hA₀ell hA₀bd hr hRmL2 hφ heq hθ0 hθ14
  rw [hc] at hdec
  -- the error term
  have hΨr : ∫ y in ball x r, ‖-Rm y‖ ^ 2 ≤
      (KT : ℝ) ^ 2 * (2 * ε) ^ 2 * ∫ y in ball x r, ‖fderiv ℝ φ y - c‖ ^ 2 := by
    rw [← integral_const_mul]
    have hi : IntegrableOn (fun y ↦ (KT : ℝ) ^ 2 * (2 * ε) ^ 2 * ‖fderiv ℝ φ y - c‖ ^ 2)
        (ball x r) :=
      (((hDL2.sub (memLp_const c)).norm.integrable_sq).const_mul _)
    refine setIntegral_mono_on hRmL2.norm.integrable_sq hi measurableSet_ball (fun y hy ↦ ?_)
    rw [norm_neg]
    have h1 := hRm_le y hy
    have h0 := norm_nonneg (Rm y)
    calc ‖Rm y‖ ^ 2 ≤ (KT * (2 * ε) * ‖fderiv ℝ φ y - c‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (KT : ℝ) ^ 2 * (2 * ε) ^ 2 * ‖fderiv ℝ φ y - c‖ ^ 2 := by ring
  have hΨ0 : 0 ≤ ∫ y in ball x r, ‖fderiv ℝ φ y - c‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hθpow : θ ^ (d + 2) = θ * θ ^ (d + 1) := by ring
  set C₁ := excessDecayConst₁ d ((Real.sqrt (1 + L ^ 2) ^ 3)⁻¹) 2 with hC₁
  set C₂ := excessDecayConst₂ d ((Real.sqrt (1 + L ^ 2) ^ 3)⁻¹) 2 with hC₂
  have hC₂0 : 0 ≤ C₂ := excessDecayConst₂_nonneg hA₀ell
  have hθd : 0 ≤ θ ^ (d + 1) := by positivity
  calc ∫ y in ball x (θ * r), ‖fderiv ℝ φ y - ⨍ z in ball x (θ * r), fderiv ℝ φ z‖ ^ 2
      ≤ C₁ * θ ^ (d + 2) * (∫ y in ball x r, ‖fderiv ℝ φ y - c‖ ^ 2) +
        C₂ * ∫ y in ball x r, ‖-Rm y‖ ^ 2 := hdec
    _ ≤ C₁ * θ ^ (d + 2) * (∫ y in ball x r, ‖fderiv ℝ φ y - c‖ ^ 2) +
        C₂ * ((KT : ℝ) ^ 2 * (2 * ε) ^ 2 * ∫ y in ball x r, ‖fderiv ℝ φ y - c‖ ^ 2) := by
        gcongr
    _ = (C₁ * θ) * θ ^ (d + 1) * (∫ y in ball x r, ‖fderiv ℝ φ y - c‖ ^ 2) +
        C₂ * ((KT : ℝ) ^ 2 * (2 * ε) ^ 2) * ∫ y in ball x r, ‖fderiv ℝ φ y - c‖ ^ 2 := by
        rw [hθpow]; ring
    _ ≤ 1 / 2 * θ ^ (d + 1) * (∫ y in ball x r, ‖fderiv ℝ φ y - c‖ ^ 2) +
        θ ^ (d + 1) / 2 * ∫ y in ball x r, ‖fderiv ℝ φ y - c‖ ^ 2 := by
        gcongr
    _ = θ ^ (d + 1) * ∫ y in ball x r, ‖fderiv ℝ φ y - c‖ ^ 2 := by ring

/-- **`C¹` solutions of the minimal surface equation are `C^{1,1/2}`** (on a ball, for a globally
Lipschitz representative). -/
theorem minimalSurface_fderiv_holder_ball (hd : 0 < d) {φ : Space d → ℝ} {Lφ : NNReal}
    (hφ : LipschitzWith Lφ φ) {x₀ : Space d} {R : ℝ} (hR : 0 < R)
    (hweak : IsWeakSolution minimalSurfaceFlux φ (ball x₀ R))
    (hcont : ContinuousOn (fderiv ℝ φ) (ball x₀ R)) :
    ∃ ρ > 0, ∃ M : ℝ, ∀ y ∈ ball x₀ ρ, ∀ z ∈ ball x₀ ρ,
      ‖fderiv ℝ φ y - fderiv ℝ φ z‖ ≤ M * dist y z ^ (1 / 2 : ℝ) := by
  set L : ℝ := (Lφ : ℝ) with hLdef
  have hL0 : 0 ≤ L := Lφ.2
  have hflux := isEllipticFlux_minimalSurfaceFlux (d := d) L
  obtain ⟨KT, hKT⟩ := exists_lipschitzOnWith_fderiv_minimalSurfaceFlux (d := d) L
  have hdiv : IsWeakDivFree (fun y ↦ minimalSurfaceFlux (gradient φ y)) (ball x₀ R) := by
    rintro ψ ⟨K, hψ⟩ hc hψU
    have := IsWeakSolution.integral_eq_zero_of_lipschitz hflux hφ le_rfl isOpen_ball hweak 0 hψ
      hc (by simpa using hψU)
    simpa using this
  have hA00 := isUniformlyElliptic_fderiv_minimalSurfaceFlux hd (L := L)
    (b := (0 : Space d)) (by simpa using hL0)
  have hCe0 := aHarmonicGradExcessConst_nonneg' hA00
  set C₁ := excessDecayConst₁ d ((Real.sqrt (1 + L ^ 2) ^ 3)⁻¹) 2 with hC₁
  set C₂ := excessDecayConst₂ d ((Real.sqrt (1 + L ^ 2) ^ 3)⁻¹) 2 with hC₂
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; unfold excessDecayConst₁; positivity
  have hC₂0 : 0 ≤ C₂ := excessDecayConst₂_nonneg hA00
  obtain ⟨θ, hθ⟩ : ∃ t : ℝ, t = min (1 / 4) (1 / (2 * C₁ + 1)) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; exact lt_min (by norm_num) (by positivity)
  have hθ14 : θ ≤ 1 / 4 := hθ ▸ min_le_left _ _
  have hθC : C₁ * θ ≤ 1 / 2 := by
    have h1 : θ ≤ 1 / (2 * C₁ + 1) := hθ ▸ min_le_right _ _
    calc C₁ * θ ≤ C₁ * (1 / (2 * C₁ + 1)) := mul_le_mul_of_nonneg_left h1 hC₁0
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
  have hθd : 0 < θ ^ (d + 1) := by positivity
  obtain ⟨ε, hε⟩ : ∃ e : ℝ, e = Real.sqrt (θ ^ (d + 1) / (8 * (C₂ * (KT : ℝ) ^ 2 + 1))) :=
    ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact Real.sqrt_pos.2 (by positivity)
  have hε2 : C₂ * ((KT : ℝ) ^ 2 * (2 * ε) ^ 2) ≤ θ ^ (d + 1) / 2 := by
    have h1 : ε ^ 2 = θ ^ (d + 1) / (8 * (C₂ * (KT : ℝ) ^ 2 + 1)) := by
      rw [hε]; exact Real.sq_sqrt (by positivity)
    have h2 : C₂ * (KT : ℝ) ^ 2 ≤ C₂ * (KT : ℝ) ^ 2 + 1 := by linarith
    calc C₂ * ((KT : ℝ) ^ 2 * (2 * ε) ^ 2) = 4 * (C₂ * (KT : ℝ) ^ 2) * ε ^ 2 := by ring
      _ = 4 * (C₂ * (KT : ℝ) ^ 2) * (θ ^ (d + 1) / (8 * (C₂ * (KT : ℝ) ^ 2 + 1))) := by rw [h1]
      _ ≤ 4 * (C₂ * (KT : ℝ) ^ 2 + 1) * (θ ^ (d + 1) / (8 * (C₂ * (KT : ℝ) ^ 2 + 1))) := by
          gcongr
      _ = θ ^ (d + 1) / 2 := by field_simp; ring
  -- uniform continuity of `Dφ`
  have hsub34 : closedBall x₀ (3 * R / 4) ⊆ ball x₀ R := closedBall_subset_ball (by linarith)
  have huc := (isCompact_closedBall x₀ (3 * R / 4)).uniformContinuousOn_of_continuous
    (hcont.mono hsub34)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε0
  obtain ⟨r₀, hr₀⟩ : ∃ r : ℝ, r = min (R / 4) (δ / 2) := ⟨_, rfl⟩
  have hr₀0 : 0 < r₀ := by rw [hr₀]; exact lt_min (by positivity) (by positivity)
  have hr₀R : r₀ ≤ R / 4 := hr₀ ▸ min_le_left _ _
  have hr₀δ : r₀ ≤ δ / 2 := hr₀ ▸ min_le_right _ _
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Space d → ℝ → ℝ, Ψ = fun x s ↦
      ∫ y in ball x s, ‖fderiv ℝ φ y - ⨍ z in ball x s, fderiv ℝ φ z‖ ^ 2 := ⟨_, rfl⟩
  have hdecay : ∀ x ∈ ball x₀ (R / 2), ∀ r, 0 < r → r ≤ r₀ →
      Ψ x (θ * r) ≤ θ ^ ((d + 1 : ℕ) : ℝ) * Ψ x r := by
    intro x hx r hr hrr₀
    have hBsub : ball x r ⊆ closedBall x₀ (3 * R / 4) := by
      intro y hy
      rw [mem_closedBall]
      have h1 := mem_ball.1 hy
      have h2 := mem_ball.1 hx
      linarith [dist_triangle y x x₀]
    have hxc : x ∈ closedBall x₀ (3 * R / 4) := hBsub (mem_ball_self hr)
    have hclose : ∀ y ∈ ball x r, ‖fderiv ℝ φ y - fderiv ℝ φ x‖ ≤ ε := by
      intro y hy
      have h1 := hδ' y (hBsub hy) x hxc (by have := mem_ball.1 hy; linarith)
      rw [dist_eq_norm] at h1
      exact h1.le
    have h := minimalSurface_excess_decay_step hd hφ hKT hr (hdiv.mono (hBsub.trans hsub34))
      hclose hθ0 hθ14 hθC hε2
    rw [Real.rpow_natCast, hΨ]
    exact h
  -- the Campanato bound
  have hθ1 : θ < 1 := by linarith
  set σ : ℝ := ((d + 1 : ℕ) : ℝ) with hσ
  have hσ0 : 0 ≤ σ := Nat.cast_nonneg _
  have hθσ : 0 < θ ^ σ := Real.rpow_pos_of_pos hθ0 _
  set ωd := volume.real (ball (0 : Space d) 1) with hωd
  have hωd0 : 0 < ωd := measureReal_unitBall_pos
  set M := Real.sqrt (16 * L ^ 2 / (θ ^ σ * r₀)) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hM2 : M ^ 2 = 16 * L ^ 2 / (θ ^ σ * r₀) := Real.sq_sqrt (by positivity)
  have hcamp : ∀ x ∈ ball x₀ (R / 2), ∀ r, 0 < r → r ≤ r₀ → closedBall x r ⊆ ball x₀ R →
      ⨍ y in ball x r, ‖fderiv ℝ φ y - ⨍ z in ball x r, fderiv ℝ φ z‖ ^ 2 ≤
        M ^ 2 * r ^ (2 * (1 / 2 : ℝ)) := by
    intro x hx r hr hrr₀ _
    have hmono : ∀ s t, 0 < s → θ * t ≤ s → s ≤ t → t ≤ r₀ → Ψ x s ≤ 4 * Ψ x t := by
      intro s t _ _ hst _
      rw [hΨ]
      have : IsFiniteMeasure (volume.restrict (ball x t)) :=
        isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
      have h1 := setIntegral_norm_sub_setAverage_sq_le
        (measure_ball_lt_top (x := x) (r := s)).ne
        (memLp_fderiv_of_lipschitz hφ _ measure_ball_lt_top.ne) (⨍ z in ball x t, fderiv ℝ φ z)
      have hit : IntegrableOn (fun y ↦ ‖fderiv ℝ φ y - ⨍ z in ball x t, fderiv ℝ φ z‖ ^ 2)
          (ball x t) :=
        ((memLp_fderiv_of_lipschitz hφ _ measure_ball_lt_top.ne).sub
          (memLp_const _)).norm.integrable_sq
      have h2 : ∫ y in ball x s, ‖fderiv ℝ φ y - ⨍ z in ball x t, fderiv ℝ φ z‖ ^ 2 ≤
          ∫ y in ball x t, ‖fderiv ℝ φ y - ⨍ z in ball x t, fderiv ℝ φ z‖ ^ 2 :=
        setIntegral_mono_set hit (Eventually.of_forall fun y ↦ sq_nonneg _)
          (ball_subset_ball hst).eventuallyLE
      simp only
      linarith only [h1, h2]
    have hΨ0 : 0 ≤ Ψ x r₀ := by rw [hΨ]; exact integral_nonneg fun _ ↦ sq_nonneg _
    have hit := le_of_excess_decay_pure (ψ := Ψ x) hθ0 hθ1 hσ0 (K := 4) (by norm_num) hr₀0 hΨ0
      hmono (hdecay x hx) hr hrr₀
    -- `Ψ(r₀) ≤ 4 L² |B_{r₀}|`
    have hΨr₀ : Ψ x r₀ ≤ 4 * (L ^ 2 * (r₀ ^ d * ωd)) := by
      have h1 := setIntegral_norm_sub_setAverage_sq_le
        (measure_ball_lt_top (x := x) (r := r₀)).ne
        (memLp_fderiv_of_lipschitz hφ _ measure_ball_lt_top.ne) 0
      simp only [sub_zero] at h1
      have h2 : ∫ y in ball x r₀, ‖fderiv ℝ φ y‖ ^ 2 ≤ L ^ 2 * (r₀ ^ d * ωd) := by
        have := norm_setIntegral_le_of_norm_le_const
          (measure_ball_lt_top (μ := volume) (x := x) (r := r₀))
          (f := fun y ↦ ‖fderiv ℝ φ y‖ ^ 2) (C := L ^ 2) (fun y _ ↦ by
            rw [Real.norm_of_nonneg (sq_nonneg _)]
            exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hφ) 2)
        rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)] at this
        refine this.trans_eq ?_
        rw [measureReal_ball_eq_mul x hr₀0]
      rw [hΨ]
      linarith only [h1, h2]
    rw [setAverage_eq, smul_eq_mul, measureReal_ball_eq_mul x hr]
    have hrd : 0 < r ^ d * ωd := by positivity
    rw [inv_mul_le_iff₀ hrd]
    have hpow : (r / r₀) ^ σ = r ^ (d + 1) / r₀ ^ (d + 1) := by
      rw [hσ, Real.rpow_natCast, div_pow]
    have hr2 : r ^ (2 * (1 / 2 : ℝ)) = r := by norm_num
    rw [hr2, hM2]
    calc ∫ y in ball x r, ‖fderiv ℝ φ y - ⨍ z in ball x r, fderiv ℝ φ z‖ ^ 2 = Ψ x r := by
          rw [hΨ]
      _ ≤ 4 / θ ^ σ * (r / r₀) ^ σ * Ψ x r₀ := hit
      _ ≤ 4 / θ ^ σ * (r / r₀) ^ σ * (4 * (L ^ 2 * (r₀ ^ d * ωd))) := by
          have : 0 ≤ (r / r₀) ^ σ := Real.rpow_nonneg (by positivity) _
          gcongr
      _ = r ^ d * ωd * (16 * L ^ 2 / (θ ^ σ * r₀) * r) := by
          rw [hpow]
          field_simp
          ring
  obtain ⟨-, -, -, hhol⟩ := campanato_fderiv_holder hφ (by linarith : R / 2 ≤ R) hr₀0
    (by norm_num : (0 : ℝ) < 1 / 2) hM0 hcamp
  set ρ := min (R / 8) (r₀ / 4) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρR : ρ ≤ R / 8 := min_le_left _ _
  have hρr : ρ ≤ r₀ / 4 := min_le_right _ _
  refine ⟨ρ, hρ0, campanatoHolderConstant d (1 / 2) * M, fun y hy z hz ↦ ?_⟩
  have hyR : y ∈ ball x₀ (R / 2) := ball_subset_ball (by linarith) hy
  have hzR : z ∈ ball x₀ (R / 2) := ball_subset_ball (by linarith) hz
  have hyz : dist y z < 2 * ρ := by
    have h1 := mem_ball.1 hy
    have h2 := mem_ball.1 hz
    linarith [dist_triangle_right y z x₀]
  have h2d : 2 * dist y z ≤ r₀ := by linarith
  have hball : closedBall y (2 * dist y z) ⊆ ball x₀ R := by
    intro w hw
    rw [mem_closedBall] at hw
    rw [mem_ball]
    have h1 := mem_ball.1 hy
    linarith [dist_triangle w y x₀]
  exact hhol y hyR z hzR h2d hball

/-- A weak solution of the minimal surface equation on `U` restricts to every closed ball in `U`
and transfers to any function agreeing with it on that ball. -/
theorem isWeakSolution_of_eqOn_closedBall {𝒜 : Space d → Space d} {φ φt : Space d → ℝ}
    {U : Set (Space d)} (hweak : IsWeakSolution 𝒜 φ U) {x : Space d} {R : ℝ}
    (hxR : closedBall x R ⊆ U) (heq : EqOn φ φt (closedBall x R)) :
    IsWeakSolution 𝒜 φt (ball x R) := by
  intro ψ hψ hψc hψB
  rw [← hweak ψ hψ hψc (hψB.trans (ball_subset_closedBall.trans hxR))]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ ball x R
  · rw [gradient_eq_of_eqOn_ball heq hy]
  · rw [gradient_eq_zero_of_notMem_tsupport (fun h ↦ hy (hψB h))]
    simp

/-- **`C¹` weak solutions of the minimal surface equation are `C^{1,1/2}`.** -/
theorem holderC_one_of_minimalSurface (hd : 0 < d) {U : Set (Space d)} (hU : IsOpen U)
    {φ : Space d → ℝ} (hφ : ContDiffOn ℝ 1 φ U)
    (hweak : IsWeakSolution minimalSurfaceFlux φ U) : HolderC (1 / 2) U 1 φ := by
  refine ⟨hφ.differentiableOn one_ne_zero, fun x hx ↦ ?_⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  have hxR : closedBall x (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  obtain ⟨K, φt, hφt, heq⟩ := exists_lipschitz_eqOn_closedBall hφ hxR
  have hweak' := isWeakSolution_of_eqOn_closedBall hweak hxR heq
  have hcont : ContinuousOn (fderiv ℝ φt) (ball x (r / 2)) := by
    have h1 : ContinuousOn (fderiv ℝ φ) (ball x (r / 2)) :=
      (hφ.continuousOn_fderiv_of_isOpen hU le_rfl).mono (ball_subset_closedBall.trans hxR)
    exact h1.congr (fun y hy ↦ (fderiv_eq_of_eqOn_ball heq hy).symm)
  obtain ⟨ρ, hρ, M, hM⟩ := minimalSurface_fderiv_holder_ball hd hφt (by positivity) hweak' hcont
  refine ⟨min ρ (r / 2), lt_min hρ (by positivity),
    (ball_subset_ball (min_le_right _ _)).trans (ball_subset_closedBall.trans hxR), M,
    fun y hy z hz ↦ ?_⟩
  have hy₁ := ball_subset_ball (min_le_left _ _) hy
  have hz₁ := ball_subset_ball (min_le_left _ _) hz
  have hy₂ := ball_subset_ball (min_le_right _ _) hy
  have hz₂ := ball_subset_ball (min_le_right _ _) hz
  rw [fderiv_eq_of_eqOn_ball heq hy₂, fderiv_eq_of_eqOn_ball heq hz₂]
  exact hM y hy₁ z hz₁

/-! ### `C^{1,γ}` solutions are `C^{2,γ/4}` -/

theorem inner_avgFluxDeriv_minimalSurfaceFlux_comm (p q ξ η : Space d) :
    inner ℝ (avgFluxDeriv minimalSurfaceFlux p q ξ) η =
      inner ℝ ξ (avgFluxDeriv minimalSurfaceFlux p q η) := by
  have hflux := isEllipticFlux_minimalSurfaceFlux (d := d) 0
  have hint : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ minimalSurfaceFlux (p + t • (q - p)))
      volume 0 1 := (hflux.continuous_fderiv_segment p q).intervalIntegrable 0 1
  have hc : ∀ v : Space d, Continuous (fun t : ℝ ↦
      fderiv ℝ minimalSurfaceFlux (p + t • (q - p)) v) := fun v ↦
    (hflux.continuous_fderiv_segment p q).clm_apply continuous_const
  rw [avgFluxDeriv, ContinuousLinearMap.intervalIntegral_apply hint,
    ContinuousLinearMap.intervalIntegral_apply hint, real_inner_comm,
    ← innerSL_apply_apply ℝ η,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ ((hc ξ).intervalIntegrable 0 1),
    ← innerSL_apply_apply ℝ ξ,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ ((hc η).intervalIntegrable 0 1)]
  congr 1
  funext t
  rw [innerSL_apply_apply, innerSL_apply_apply, real_inner_comm,
    inner_fderiv_minimalSurfaceFlux_comm]

theorem norm_avgFluxDeriv_minimalSurfaceFlux_sub_le {L : ℝ} {K : NNReal}
    (hK : LipschitzOnWith K (fderiv ℝ (minimalSurfaceFlux (d := d))) (closedBall 0 L))
    {p q p' q' : Space d} (hp : ‖p‖ ≤ L) (hq : ‖q‖ ≤ L) (hp' : ‖p'‖ ≤ L) (hq' : ‖q'‖ ≤ L) :
    ‖avgFluxDeriv minimalSurfaceFlux p q - avgFluxDeriv minimalSurfaceFlux p' q'‖ ≤
      K * (‖p - p'‖ + ‖q - q'‖) := by
  have hflux := isEllipticFlux_minimalSurfaceFlux (d := d) 0
  have hint1 : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ minimalSurfaceFlux (p + t • (q - p)))
      volume 0 1 := (hflux.continuous_fderiv_segment p q).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ minimalSurfaceFlux (p' + t • (q' - p')))
      volume 0 1 := (hflux.continuous_fderiv_segment p' q').intervalIntegrable 0 1
  rw [avgFluxDeriv, avgFluxDeriv, ← intervalIntegral.integral_sub hint1 hint2]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := K * (‖p - p'‖ + ‖q - q'‖))
    (f := fun t : ℝ ↦ fderiv ℝ minimalSurfaceFlux (p + t • (q - p)) -
      fderiv ℝ minimalSurfaceFlux (p' + t • (q' - p'))) (fun t ht ↦ by
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
      have h1 := hK.dist_le_mul _ (mem_closedBall_segment_aux hp hq ht') _
        (mem_closedBall_segment_aux hp' hq' ht')
      rw [dist_eq_norm, dist_eq_norm] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ K.2)
      have e : p + t • (q - p) - (p' + t • (q' - p')) = (1 - t) • (p - p') + t • (q - q') := by
        simp only [smul_sub, sub_smul, one_smul]
        abel
      rw [e]
      calc ‖(1 - t) • (p - p') + t • (q - q')‖ ≤ ‖(1 - t) • (p - p')‖ + ‖t • (q - q')‖ :=
            norm_add_le _ _
        _ = (1 - t) * ‖p - p'‖ + t * ‖q - q'‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht'.2]),
              Real.norm_of_nonneg ht'.1]
        _ ≤ ‖p - p'‖ + ‖q - q'‖ := by
            nlinarith [norm_nonneg (p - p'), norm_nonneg (q - q'), ht'.1, ht'.2])
  rwa [sub_zero, abs_one, mul_one] at h

/-- **`C^{1,γ}` solutions of the minimal surface equation are `C^{2,γ/4}`** (on a ball, for a
globally Lipschitz representative, one direction at a time). -/
theorem minimalSurface_partial_holder_ball (hd : 0 < d) {φ : Space d → ℝ} {Lφ : NNReal}
    (hφ : LipschitzWith Lφ φ) {x₀ : Space d} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hweak : IsWeakSolution minimalSurfaceFlux φ (ball x₀ R₀))
    (hdiff : ∀ y ∈ ball x₀ R₀, DifferentiableAt ℝ φ y) {γ H : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hH : 0 ≤ H)
    (hhol : ∀ y ∈ ball x₀ R₀, ∀ z ∈ ball x₀ R₀, ‖fderiv ℝ φ y - fderiv ℝ φ z‖ ≤ H * dist y z ^ γ)
    {e : Space d} (he : ‖e‖ ≤ 1) :
    ∃ ρ > 0, ∃ M, 0 ≤ M ∧
      (∀ y ∈ ball x₀ ρ, DifferentiableAt ℝ (fun z ↦ fderiv ℝ φ z e) y) ∧
      ∀ y ∈ ball x₀ ρ, ∀ z ∈ ball x₀ ρ, ‖fderiv ℝ (fun z ↦ fderiv ℝ φ z e) y -
        fderiv ℝ (fun z ↦ fderiv ℝ φ z e) z‖ ≤ M * dist y z ^ (γ / 4) := by
  have hL0 : (0 : ℝ) ≤ Lφ := Lφ.2
  have hflux := isEllipticFlux_minimalSurfaceFlux (d := d) (Lφ : ℝ)
  obtain ⟨KT, hKT⟩ := exists_lipschitzOnWith_fderiv_minimalSurfaceFlux (d := d) (Lφ : ℝ)
  set ν : ℝ := (Real.sqrt (1 + (Lφ : ℝ) ^ 2) ^ 3)⁻¹ with hνdef
  have hν : 0 < ν := by positivity
  have hν2 : ν ≤ 2 := by
    have h1 : 1 ≤ Real.sqrt (1 + (Lφ : ℝ) ^ 2) := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (1 + (Lφ : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Lφ : ℝ)])
    have := inv_le_one_of_one_le₀ (one_le_pow₀ (n := 3) h1)
    linarith
  have hgradL : ∀ y, ‖gradient φ y‖ ≤ (Lφ : ℝ) := fun y ↦ by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hφ
  set R := R₀ / 4 with hRdef
  have hR : 0 < R := by positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ → Space d → Space d →L[ℝ] Space d, a = fun h y ↦
      avgFluxDeriv minimalSurfaceFlux (gradient φ y) (gradient φ (y + h • e)) := ⟨_, rfl⟩
  have hshift : ∀ h, |h| < R → ∀ y ∈ ball x₀ (2 * R), y + h • e ∈ ball x₀ R₀ := by
    intro h hh y hy
    rw [mem_ball] at hy ⊢
    have h1 : ‖h • e‖ ≤ |h| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg h) he
    calc dist (y + h • e) x₀ ≤ dist y x₀ + ‖h • e‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
          exact norm_add_le _ _
      _ < R₀ := by linarith
  have hball2 : ball x₀ (2 * R) ⊆ ball x₀ R₀ := ball_subset_ball (by linarith)
  -- the difference-quotient equations on `ball x₀ (2R)`
  have hDQeq : ∀ h, h ≠ 0 → |h| < R → IsWeakDivFree
      (fun y ↦ a h y (gradient (diffQuot φ e h) y) - 0) (ball x₀ (2 * R)) := by
    intro h hh hhR
    have hgm : Measurable (gradient φ) :=
      (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
    have ham : Measurable (fun y ↦ a h y) := by
      have hpair : Measurable (fun y : Space d ↦ (gradient φ y, gradient φ (y + h • e))) :=
        hgm.prodMk (hgm.comp (measurable_add_const (h • e)))
      have hcomp := hflux.continuous_avgFluxDeriv.measurable.comp hpair
      rw [ha]
      exact hcomp
    have hwm : Measurable (gradient (diffQuot φ e h)) :=
      (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)
    have hwL := lipschitzWith_diffQuot hφ e h
    have hbound : ∀ y, ‖a h y (gradient (diffQuot φ e h) y) - 0‖ ≤
        2 * (Real.toNNReal (|h|⁻¹ * (2 * Lφ)) : ℝ) := by
      intro y
      rw [sub_zero]
      have hay : ‖a h y‖ ≤ 2 := by rw [ha]; exact hflux.norm_avgFluxDeriv_le (hgradL y) (hgradL _)
      refine ((a h y).le_opNorm _).trans (mul_le_mul hay ?_ (norm_nonneg _) zero_le_two)
      rw [norm_gradient_eq_norm_fderiv]
      exact norm_fderiv_le_of_lipschitz ℝ hwL
    refine IsWeakDivFree.of_smooth isOpen_ball ?_ (fun ψ hψ hψc hψB ↦ ?_)
    · exact (Measure.integrableOn_of_bounded (M := 2 * (Real.toNNReal (|h|⁻¹ * (2 * Lφ)) : ℝ))
        measure_ball_lt_top.ne
        (((ContinuousLinearMap.id ℝ (Space d →L[ℝ] Space d)).aestronglyMeasurable_comp₂
          ham.aestronglyMeasurable hwm.aestronglyMeasurable).sub aestronglyMeasurable_const)
        (Eventually.of_forall hbound)).locallyIntegrableOn
    · have hsubh : tsupport ψ ⊆ (· + h • e) ⁻¹' ball x₀ R₀ := fun y hy ↦
        hshift h hhR y (hψB hy)
      have h1 := IsWeakSolution.integral_inner_avgFluxDeriv_eq_zero hflux hφ hweak e (h := h)
        (φ := ψ) (hψ.of_le (by simp)) hψc (hψB.trans hball2) hsubh
      rw [ha]
      simpa only [sub_zero] using h1
  -- structure conditions on `ball x₀ (2R)`
  have hsymm : ∀ h, h ≠ 0 → |h| < R → ∀ y ∈ ball x₀ R, ∀ v w,
      inner ℝ (a h y v) w = inner ℝ v (a h y w) := by
    intro h _ _ y _ v w
    rw [ha]
    exact inner_avgFluxDeriv_minimalSurfaceFlux_comm _ _ v w
  have hell2 : ∀ h, ∀ y, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a h y ξ) ξ := by
    intro h y ξ
    rw [ha]
    exact hflux.inner_avgFluxDeriv_ge (hgradL y) (hgradL _) ξ
  have hbd2 : ∀ h, ∀ y, ‖a h y‖ ≤ 2 := by
    intro h y
    rw [ha]
    exact hflux.norm_avgFluxDeriv_le (hgradL y) (hgradL _)
  have hhol2 : ∀ h, h ≠ 0 → |h| < R → ∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R,
      ‖a h y - a h y'‖ ≤ (2 * KT * H) * dist y y' ^ γ := by
    intro h _ hhR y hy y' hy'
    have hy2 : y ∈ ball x₀ (2 * R) := ball_subset_ball (by linarith) hy
    have hy2' : y' ∈ ball x₀ (2 * R) := ball_subset_ball (by linarith) hy'
    rw [ha]
    have h1 := norm_avgFluxDeriv_minimalSurfaceFlux_sub_le hKT (hgradL y) (hgradL (y + h • e))
      (hgradL y') (hgradL (y' + h • e))
    have h2 : ‖gradient φ y - gradient φ y'‖ ≤ H * dist y y' ^ γ := by
      rw [gradient, gradient, ← map_sub, LinearIsometryEquiv.norm_map]
      exact hhol y (hball2 hy2) y' (hball2 hy2')
    have h3 : ‖gradient φ (y + h • e) - gradient φ (y' + h • e)‖ ≤ H * dist y y' ^ γ := by
      rw [gradient, gradient, ← map_sub, LinearIsometryEquiv.norm_map]
      have := hhol (y + h • e) (hshift h hhR y hy2) (y' + h • e) (hshift h hhR y' hy2')
      rwa [dist_add_right] at this
    calc ‖avgFluxDeriv minimalSurfaceFlux (gradient φ y) (gradient φ (y + h • e)) -
          avgFluxDeriv minimalSurfaceFlux (gradient φ y') (gradient φ (y' + h • e))‖ ≤
        KT * (‖gradient φ y - gradient φ y'‖ +
          ‖gradient φ (y + h • e) - gradient φ (y' + h • e)‖) := h1
      _ ≤ KT * (H * dist y y' ^ γ + H * dist y y' ^ γ) := by gcongr
      _ = (2 * KT * H) * dist y y' ^ γ := by ring
  -- uniform energy bound on `ball x₀ R`
  set E : ℝ := 2 / ν * ((4 * 2 ^ 2 / ν + 1) * (2 / (2 * R - R)) ^ 2 *
    ((Lφ : ℝ) ^ 2 * volume.real (ball x₀ (2 * R)))) with hEdef
  have hE0 : 0 ≤ E := by
    have := measureReal_nonneg (μ := volume) (s := ball x₀ (2 * R))
    positivity
  have hE : ∀ h, h ≠ 0 → |h| < R →
      ∫ y in ball x₀ R, ‖fderiv ℝ (diffQuot φ e h) y‖ ^ 2 ≤ E := by
    intro h hh hhR
    have hwL := lipschitzWith_diffQuot hφ e h
    have hgm : Measurable (gradient φ) :=
      (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
    have ham : AEStronglyMeasurable (a h) (volume.restrict (ball x₀ (2 * R))) := by
      have hpair : Measurable (fun y : Space d ↦ (gradient φ y, gradient φ (y + h • e))) :=
        hgm.prodMk (hgm.comp (measurable_add_const (h • e)))
      have hcomp := hflux.continuous_avgFluxDeriv.measurable.comp hpair
      rw [ha]
      exact hcomp.aestronglyMeasurable
    have hcac := caccioppoli (a := a h) (Λ := 2) hν (x₀ := x₀) (ρ := R) (s := 2 * R)
      (by linarith) ham (fun y _ ξ ↦ hell2 h y ξ) (fun y _ ↦ hbd2 h y)
      (G := fun _ ↦ (0 : Space d)) (MemLp.zero) hwL (hDQeq h hh hhR)
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero, mul_zero, add_zero] at hcac
    have hw2 : ∫ y in ball x₀ (2 * R), diffQuot φ e h y ^ 2 ≤
        (Lφ : ℝ) ^ 2 * volume.real (ball x₀ (2 * R)) := by
      have := norm_setIntegral_le_of_norm_le_const
        (measure_ball_lt_top (μ := volume) (x := x₀) (r := 2 * R))
        (f := fun y ↦ diffQuot φ e h y ^ 2) (C := (Lφ : ℝ) ^ 2) (fun y _ ↦ by
          rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
          have h1 := abs_diffQuot_le hφ e hh y
          have h2 : (Lφ : ℝ) * ‖e‖ ≤ Lφ := mul_le_of_le_one_right Lφ.2 he
          exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)] at this
      exact this
    simp only [norm_gradient_eq_norm_fderiv] at hcac
    refine hcac.trans ?_
    rw [hEdef]
    gcongr
  have hu : ∀ y ∈ ball x₀ R, DifferentiableAt ℝ φ y := fun y hy ↦
    hdiff y (ball_subset_ball (by linarith) hy)
  obtain ⟨ρ, hρ, -, M, hM0, hdM, hholM⟩ := holder_partial_of_diffQuot hd hγ0 hγ1 hν hν2 hR
    (by positivity : (0 : ℝ) ≤ 2 * KT * H) e hu hR le_rfl hE0 a (fun _ _ ↦ 0) hsymm
    (fun h _ _ y _ ξ ↦ hell2 h y ξ) (fun h _ _ y _ ↦ hbd2 h y) hhol2
    (fun _ _ _ _ _ _ _ ↦ by simp)
    (fun h _ ↦ ⟨_, lipschitzWith_diffQuot hφ e h⟩)
    (fun h hh hhR ↦ (hDQeq h hh hhR).mono (ball_subset_ball (by linarith))) hE
  exact ⟨ρ, hρ, M, hM0, hdM, hholM⟩

/-- **`C^{1,γ}` weak solutions of the minimal surface equation are `C^{2,γ/4}`.** -/
theorem holderC_two_of_minimalSurface (hd : 0 < d) {U : Set (Space d)} (hU : IsOpen U)
    {φ : Space d → ℝ} {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hφ : HolderC γ U 1 φ)
    (hweak : IsWeakSolution minimalSurfaceFlux φ U) : HolderC (γ / 4) U 2 φ := by
  have hφ1 : ContDiffOn ℝ 1 φ U := HolderC.contDiffOn hγ0 hU hφ
  refine holderC_succ_of_partials hU hφ.1 (fun i ↦ ?_)
  set v : Space d := EuclideanSpace.single i 1 with hv
  have hv1 : ‖v‖ ≤ 1 := by rw [hv]; simp
  have hloc : ∀ x ∈ U, ∃ ρ > 0, ball x ρ ⊆ U ∧ ∃ M,
      (∀ y ∈ ball x ρ, DifferentiableAt ℝ (fun z ↦ fderiv ℝ φ z v) y) ∧
      ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖fderiv ℝ (fun z ↦ fderiv ℝ φ z v) y -
        fderiv ℝ (fun z ↦ fderiv ℝ φ z v) z‖ ≤ M * dist y z ^ (γ / 4) := by
    intro x hx
    obtain ⟨r, hr, hrU, Mh, hMh⟩ := hφ.2 x hx
    have hR₀ : 0 < r / 2 := by positivity
    have hxR : closedBall x (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
    obtain ⟨K, φt, hφt, heq⟩ := exists_lipschitz_eqOn_closedBall hφ1 hxR
    have hweak' := isWeakSolution_of_eqOn_closedBall hweak hxR heq
    have hev : ∀ y ∈ ball x (r / 2), φ =ᶠ[𝓝 y] φt := fun y hy ↦ by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact heq (ball_subset_closedBall hz)
    have hdiff' : ∀ y ∈ ball x (r / 2), DifferentiableAt ℝ φt y := fun y hy ↦
      (hev y hy).differentiableAt_iff.1 ((hφ.1 y (hxR (ball_subset_closedBall hy))).differentiableAt
        (hU.mem_nhds (hxR (ball_subset_closedBall hy))))
    have hhol' : ∀ y ∈ ball x (r / 2), ∀ z ∈ ball x (r / 2),
        ‖fderiv ℝ φt y - fderiv ℝ φt z‖ ≤ max Mh 0 * dist y z ^ γ := by
      intro y hy z hz
      rw [← fderiv_eq_of_eqOn_ball heq hy, ← fderiv_eq_of_eqOn_ball heq hz]
      exact (hMh y (ball_subset_ball (by linarith) hy) z (ball_subset_ball (by linarith) hz)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
    obtain ⟨ρ, hρ, M, -, hdM, hholM⟩ := minimalSurface_partial_holder_ball hd hφt hR₀ hweak'
      hdiff' hγ0 hγ1 (le_max_right Mh 0) hhol' hv1
    have hev' : ∀ y ∈ ball x (r / 2), (fun z ↦ fderiv ℝ φ z v) =ᶠ[𝓝 y]
        (fun z ↦ fderiv ℝ φt z v) := fun y hy ↦ by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      rw [fderiv_eq_of_eqOn_ball heq hz]
    refine ⟨min ρ (r / 2), lt_min hρ hR₀,
      (ball_subset_ball (min_le_right _ _)).trans (ball_subset_closedBall.trans hxR), M,
      fun y hy ↦ ?_, fun y hy z hz ↦ ?_⟩
    · have hy₂ := ball_subset_ball (min_le_right _ _) hy
      exact ((hev' y hy₂).differentiableAt_iff).2 (hdM y (ball_subset_ball (min_le_left _ _) hy))
    · have hy₂ := ball_subset_ball (min_le_right _ _) hy
      have hz₂ := ball_subset_ball (min_le_right _ _) hz
      rw [(hev' y hy₂).fderiv_eq, (hev' z hz₂).fderiv_eq]
      exact hholM y (ball_subset_ball (min_le_left _ _) hy) z (ball_subset_ball (min_le_left _ _) hz)
  refine ⟨fun y hy ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨ρ, hρ, -, -, hdM, -⟩ := hloc y hy
    exact (hdM y (mem_ball_self hρ)).differentiableWithinAt
  · obtain ⟨ρ, hρ, hρU, M, -, hholM⟩ := hloc x hx
    exact ⟨ρ, hρ, hρU, M, hholM⟩

/-! ### Higher regularity and smoothness -/

/-- A `C¹` weak solution of the minimal surface equation is weakly divergence free against
Lipschitz tests. -/
theorem IsWeakSolution.isWeakDivFree_minimalSurface {U : Set (Space d)} (hU : IsOpen U)
    {φ : Space d → ℝ} (hφ : ContDiffOn ℝ 1 φ U)
    (hweak : IsWeakSolution minimalSurfaceFlux φ U) :
    IsWeakDivFree (fun y ↦ minimalSurfaceFlux (gradient φ y)) U := by
  have hgc : ContinuousOn (gradient φ) U :=
    (toDual ℝ (Space d)).symm.continuous.comp_continuousOn
      (hφ.continuousOn_fderiv_of_isOpen hU le_rfl)
  refine IsWeakDivFree.of_smooth hU ((contDiff_minimalSurfaceFlux.continuous.comp_continuousOn
    hgc).locallyIntegrableOn hU.measurableSet) (fun ψ hψ hψc hψU ↦ ?_)
  exact hweak ψ (hψ.of_le (by simp)) hψc hψU

/-- **The linearized equation**: the directional derivatives of a `C²` weak solution of the
minimal surface equation solve `div (DA(∇φ) ∇∂ₑφ) = 0`. -/
theorem isWeakDivFree_linearized_minimalSurface {U : Set (Space d)} (hU : IsOpen U)
    {φ : Space d → ℝ} (hφ : ContDiffOn ℝ 2 φ U)
    (hweak : IsWeakSolution minimalSurfaceFlux φ U) (e : Space d) :
    IsWeakDivFree (fun y ↦ fderiv ℝ minimalSurfaceFlux (gradient φ y)
      (gradient (fun z ↦ fderiv ℝ φ z e) y) - 0) U := by
  have hφ1 : ContDiffOn ℝ 1 φ U := hφ.of_le (by norm_num)
  have hdiv := hweak.isWeakDivFree_minimalSurface hU hφ1
  have hgrad : ContDiffOn ℝ 1 (gradient φ) U := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
    exact (toDual ℝ (Space d)).symm.contDiff.comp_contDiffOn h1
  have hV : ContDiffOn ℝ 1 (fun y ↦ minimalSurfaceFlux (gradient φ y)) U :=
    contDiff_minimalSurfaceFlux.comp_contDiffOn hgrad
  refine (hdiv.fderiv_apply hU hV e).congr_ae (Eventually.of_forall fun y hy ↦ ?_)
  have hgy : DifferentiableAt ℝ (gradient φ) y :=
    (hgrad.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
  have h2 : ContDiffAt ℝ 2 φ y := (hφ y hy).contDiffAt (hU.mem_nhds hy)
  have hA : DifferentiableAt ℝ minimalSurfaceFlux (gradient φ y) :=
    contDiff_minimalSurfaceFlux.differentiable one_ne_zero _
  rw [fderiv_fun_comp y hA hgy, ContinuousLinearMap.comp_apply, fderiv_gradient_apply h2 e, sub_zero]

/-- **One step of the bootstrap**: a `C^{m+2,γ}` weak solution of the minimal surface equation
is `C^{m+3,γ'}`. -/
theorem minimalSurface_holderC_succ_succ (hd : 0 < d) {U : Set (Space d)} (hU : IsOpen U)
    {φ : Space d → ℝ} (hweak : IsWeakSolution minimalSurfaceFlux φ U) {m : ℕ} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hφ : HolderC γ U (m + 2) φ) :
    ∃ γ', 0 < γ' ∧ γ' ≤ 1 ∧ HolderC γ' U (m + 3) φ := by
  obtain ⟨γ', hγ'0, hγ'1, hLR⟩ := linearRegularity hd (m + 1) γ hγ0 hγ1
  refine ⟨γ', hγ'0, hγ'1, holderC_succ_of_partials hU hφ.1 (fun i ↦ ?_)⟩
  set e : Space d := EuclideanSpace.single i 1 with he
  have hφ2 : ContDiffOn ℝ 2 φ U := (HolderC.contDiffOn hγ0 hU hφ).of_le (by norm_cast; omega)
  have hlin := isWeakDivFree_linearized_minimalSurface hU hφ2 hweak e
  have hDφ : HolderC γ U (m + 1) (fderiv ℝ φ) := hφ.2
  have hDφc : ContinuousOn (fderiv ℝ φ) U := HolderC.continuousOn hγ0 hDφ
  have hpart : HolderC γ U (m + 1) (fun y ↦ fderiv ℝ φ y e) := HolderC.fderiv_apply hU hφ e
  have hcoef : HolderC γ U (m + 1)
      (fun y ↦ fderiv ℝ minimalSurfaceFlux ((toDual ℝ (Space d)).symm (fderiv ℝ φ y))) := by
    have hΦ : ContDiff ℝ ∞ (fun L : Space d →L[ℝ] ℝ ↦
        fderiv ℝ minimalSurfaceFlux ((toDual ℝ (Space d)).symm L)) :=
      (contDiff_minimalSurfaceFlux_infty.fderiv_right (m := ∞) (by simp)).comp
        (toDual ℝ (Space d)).symm.contDiff
    exact HolderC.comp_contDiff (f := fderiv ℝ φ)
      (Φ := fun L : Space d →L[ℝ] ℝ ↦ fderiv ℝ minimalSurfaceFlux ((toDual ℝ (Space d)).symm L))
      hγ0 hγ1 hU hΦ hDφ
  refine holderC_of_forall_ball (fun x hx ↦ ?_)
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  have hxr : closedBall x (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hB : ball x (r / 2) ⊆ U := ball_subset_closedBall.trans hxr
  obtain ⟨L, hL⟩ := (isCompact_closedBall x (r / 2)).exists_bound_of_continuousOn
    (hDφc.mono hxr)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL x (mem_closedBall_self (by positivity)))
  have hgL : ∀ y ∈ ball x (r / 2), ‖gradient φ y‖ ≤ L := fun y hy ↦ by
    rw [norm_gradient_eq_norm_fderiv]
    exact hL y (ball_subset_closedBall hy)
  have hν : 0 < (Real.sqrt (1 + L ^ 2) ^ 3)⁻¹ := by positivity
  have hν2 : (Real.sqrt (1 + L ^ 2) ^ 3)⁻¹ ≤ 2 := by
    have h1 : 1 ≤ Real.sqrt (1 + L ^ 2) := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (1 + L ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg L])
    have := inv_le_one_of_one_le₀ (one_le_pow₀ (n := 3) h1)
    linarith
  have hflux := isEllipticFlux_minimalSurfaceFlux (d := d) L
  have hu1 : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ φ y e) (ball x (r / 2)) :=
    ((HolderC.contDiffOn hγ0 hU hpart).of_le (by norm_cast; omega)).mono hB
  refine ⟨r / 2, by positivity, hB, hLR (ball x (r / 2)) _ 2
    (fun y ↦ fderiv ℝ minimalSurfaceFlux ((toDual ℝ (Space d)).symm (fderiv ℝ φ y)))
    (fun _ ↦ 0) _ isOpen_ball hν hν2
    (fun y _ v w ↦ inner_fderiv_minimalSurfaceFlux_comm _ v w)
    (fun y hy ξ ↦ hflux.elliptic _ (hgL y hy) ξ)
    (fun y _ ↦ norm_fderiv_minimalSurfaceFlux_le _)
    (HolderC.mono_set hB isOpen_ball hcoef) (holderC_const isOpen_ball 0) hu1
    (hlin.mono hB)⟩

/-- **Smoothness of `C¹` weak solutions of the minimal surface equation.** If `φ` is `C¹` on an
open set `U ⊆ ℝ^d` and `∫ ⟪∇φ / √(1 + |∇φ|²), ∇ψ⟫ = 0` for every `C¹` function `ψ` compactly
supported in `U`, then `φ` is `C^∞` on `U`. -/
theorem contDiffOn_infty_of_weak_minimalSurface_of_pos (hd : 0 < d) {U : Set (Space d)}
    (hU : IsOpen U) {φ : Space d → ℝ} (hφ : ContDiffOn ℝ 1 φ U)
    (hweak : IsWeakSolution minimalSurfaceFlux φ U) : ContDiffOn ℝ ∞ φ U := by
  have h : ∀ m : ℕ, IsHolderC U (m + 2) φ := by
    intro m
    induction m with
    | zero =>
      exact ⟨1 / 2 / 4, by norm_num, by norm_num, holderC_two_of_minimalSurface hd hU
        (by norm_num) (by norm_num) (holderC_one_of_minimalSurface hd hU hφ hweak) hweak⟩
    | succ m ih =>
      obtain ⟨γ, hγ0, hγ1, hm⟩ := ih
      obtain ⟨γ', hγ'0, hγ'1, hm'⟩ := minimalSurface_holderC_succ_succ hd hU hweak hγ0 hγ1 hm
      exact ⟨γ', hγ'0, hγ'1, hm'⟩
  refine contDiffOn_infty_of_isHolderC hU (fun k ↦ ?_)
  obtain ⟨γ, hγ0, hγ1, hk⟩ := h k
  exact ⟨γ, hγ0, hγ1, HolderC.of_le hγ0 hγ1 hU (by omega) hk⟩

/-- **Smoothness of `C¹` weak solutions of the minimal surface equation** (any dimension). If `φ`
is `C¹` on an open set `U ⊆ ℝ^d` and `∫ ⟪∇φ / √(1 + |∇φ|²), ∇ψ⟫ = 0` for every `C¹` function `ψ`
compactly supported in `U` (`IsWeakSolution minimalSurfaceFlux φ U`), then `φ` is `C^∞` on
`U`. -/
theorem contDiffOn_infty_of_weak_minimalSurface {U : Set (Space d)} (hU : IsOpen U)
    {φ : Space d → ℝ} (hφ : ContDiffOn ℝ 1 φ U)
    (hweak : IsWeakSolution minimalSurfaceFlux φ U) : ContDiffOn ℝ ∞ φ U := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h : φ = fun _ ↦ φ 0 := by
      funext y
      congr 1
      ext i
      exact i.elim0
    rw [h]
    exact contDiffOn_const
  · exact contDiffOn_infty_of_weak_minimalSurface_of_pos hd hU hφ hweak

/-- The same statement with the weak minimal surface equation written out. -/
theorem contDiffOn_infty_of_weak_minimalSurface' {U : Set (Space d)} (hU : IsOpen U)
    {φ : Space d → ℝ} (hφ : ContDiffOn ℝ 1 φ U)
    (hweak : ∀ ψ : Space d → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ y, inner ℝ ((Real.sqrt (1 + ‖gradient φ y‖ ^ 2))⁻¹ • gradient φ y) (gradient ψ y) = 0) :
    ContDiffOn ℝ ∞ φ U :=
  contDiffOn_infty_of_weak_minimalSurface hU hφ hweak

/-- **Schauder for the minimal surface equation** (the form used in `RigidityReduction`): a `C¹`
weak solution of the minimal surface equation on a ball is `C^∞` on that ball. -/
theorem minimalSurface_contDiffOn_top_proof (m : ℕ) (ρ : ℝ) (φ : Space m → ℝ) (_hm : 0 < m)
    (_hρ : 0 < ρ) (hφ : ContDiffOn ℝ 1 φ (ball 0 ρ))
    (hweak : IsWeakSolution minimalSurfaceFlux φ (ball 0 ρ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) φ (ball 0 ρ) :=
  contDiffOn_infty_of_weak_minimalSurface isOpen_ball hφ hweak

end SerrinEpigraph
