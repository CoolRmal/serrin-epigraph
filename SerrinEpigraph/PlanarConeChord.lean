module

public import SerrinEpigraph.SimonsCone
public import SerrinEpigraph.GraphPerimeter

/-!
# The chord argument for planar minimizing cones

* **Removable points** (`Planar.variationalPerimeter_le_diff_singleton`): in dimension `d ≥ 2`,
  removing a point from the test domain does not change the variational perimeter.
* **Perimeter of affine epigraphs in the plane** (`Planar.perimeter_epigraph_affine`): the
  perimeter of `{x₂ > κ x₁ + c}` in an open set is `√(1 + κ²)` times the length of the parameter
  set of the line inside the open set.
* **The chord contradiction** (`Planar.chord_false`): a minimizing cone in the plane cannot agree,
  on a sector `{κ' |x₁| < x₂}`, with a narrower convex sector `{κ |x₁| < x₂}` (`0 < κ' < κ`).
  Cutting off the tip `{κ |x₁| < x₂ < 1}` replaces two segments of length `√(1+κ²)/κ` by a chord
  of length `2/κ`, while the error near the vertex is `O(ρ)` by the upper density bound.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff ENNReal

namespace SerrinEpigraph

namespace Planar

/-! ### 1. Removable points -/

theorem fieldDivergence_smul {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {χ : Space d → ℝ} {F : Space d → Space d} {x : Space d}
    (hχ : DifferentiableAt ℝ χ x) (hF : DifferentiableAt ℝ F x) :
    fieldDivergence b (fun y ↦ χ y • F y) x =
      χ x * fieldDivergence b F x + fderiv ℝ χ x (F x) := by
  have hd : HasFDerivAt (fun y ↦ χ y • F y)
      (χ x • fderiv ℝ F x + (fderiv ℝ χ x).smulRight (F x)) x :=
    hχ.hasFDerivAt.smul hF.hasFDerivAt
  have hsum : ∑ i, fderiv ℝ χ x (b i) * inner ℝ (b i) (F x) = fderiv ℝ χ x (F x) := by
    conv_rhs => rw [← b.sum_repr' (F x)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [fieldDivergence, hd.fderiv, fieldDivergence, Finset.mul_sum, ← hsum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, inner_add_right, real_inner_smul_right]

/-- **Removable points.** In dimension at least two a point can be removed from the test domain
of the variational perimeter. -/
theorem variationalPerimeter_le_diff_singleton {d : ℕ} (hd : 2 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    (Ω : Set (Space d)) (p : Space d) :
    variationalPerimeter b E Ω ≤ variationalPerimeter b E (Ω \ {p}) := by
  conv_lhs => unfold variationalPerimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦ iSup_le fun hs ↦ iSup_le fun hu ↦ ?_
  set r : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hrdef
  have hr : ∀ n, 0 < r n := fun n ↦ by positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set χ : ℕ → Space d → ℝ := fun n ↦ doubledBallCutoff p (r n) with hχdef
  have hχs : ∀ n, ContDiff ℝ 1 (χ n) := fun n ↦
    (contDiff_doubledBallCutoff p (r n)).of_le (by simp)
  set u : Space d → ℝ := E.indicator (fun _ ↦ (1 : ℝ)) with hudef
  have hum : Measurable u := measurable_const.indicator hE
  have hub : ∀ x, ‖u x‖ ≤ 1 := fun x ↦ by
    by_cases hx : x ∈ E <;> simp [hudef, hx]
  -- admissibility of the cut-off fields
  have hadm : ∀ n, ENNReal.ofReal ‖∫ x, u x * fieldDivergence b (fun y ↦ χ n y • F y) x‖ ≤
      variationalPerimeter b E (Ω \ {p}) := by
    intro n
    unfold variationalPerimeter
    refine le_iSup_of_le (fun y ↦ χ n y • F y) (le_iSup_of_le ((hχs n).smul hF)
      (le_iSup_of_le (hc.smul_left (f := χ n)) (le_iSup_of_le ?_ (le_iSup_of_le ?_ le_rfl))))
    · intro x hx
      refine ⟨hs (tsupport_smul_subset_right _ _ hx), ?_⟩
      rintro rfl
      have hp : x ∉ tsupport (fun y ↦ χ n y • F y) := by
        rw [notMem_tsupport_iff_eventuallyEq]
        filter_upwards [ball_mem_nhds x (hr n)] with y hy
        rw [mem_ball, dist_eq_norm] at hy
        simp only [hχdef, Pi.zero_apply]
        rw [doubledBallCutoff_eq_zero (hr n) hy.le, zero_smul]
      exact hp hx
    · intro x
      rw [norm_smul, Real.norm_of_nonneg (doubledBallCutoff_nonneg _ _ _)]
      calc χ n x * ‖F x‖ ≤ 1 * 1 :=
            mul_le_mul (doubledBallCutoff_le_one _ _ _) (hu x) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have hdiv : ∀ n x, fieldDivergence b (fun y ↦ χ n y • F y) x =
      χ n x * fieldDivergence b F x + fderiv ℝ (χ n) x (F x) := fun n x ↦
    fieldDivergence_smul b ((hχs n).differentiable one_ne_zero x) (hF.differentiable one_ne_zero x)
  -- integrability
  have hdc : Continuous (fieldDivergence b F) := fieldDivergence_continuous b hF
  have hdcs : HasCompactSupport (fieldDivergence b F) := by
    refine hc.mono' fun x hx ↦ ?_
    by_contra hxF
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hxF)
  have hdi : Integrable (fieldDivergence b F) := hdc.integrable_of_hasCompactSupport hdcs
  have hχc : ∀ n, Continuous (χ n) := fun n ↦ (hχs n).continuous
  have hDχc : ∀ n, Continuous (fderiv ℝ (χ n)) := fun n ↦
    (contDiff_doubledBallCutoff p (r n)).continuous_fderiv (by simp)
  have hint1 : ∀ n, Integrable (fun x ↦ u x * (χ n x * fieldDivergence b F x)) := by
    intro n
    refine hdi.norm.mono' ((hum.mul ((hχc n).mul hdc).measurable).aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ ?_)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (doubledBallCutoff_nonneg _ _ _)]
    calc ‖u x‖ * (χ n x * ‖fieldDivergence b F x‖) ≤ 1 * (1 * ‖fieldDivergence b F x‖) :=
          mul_le_mul (hub x) (mul_le_mul_of_nonneg_right (doubledBallCutoff_le_one _ _ _)
            (norm_nonneg _)) (mul_nonneg (doubledBallCutoff_nonneg _ _ _) (norm_nonneg _))
            zero_le_one
      _ = ‖fieldDivergence b F x‖ := by ring
  set K := cutoffStepDerivBound with hKdef
  have hK : 0 ≤ K := cutoffStepDerivBound_nonneg
  have hbnd : ∀ n x, ‖u x * fderiv ℝ (χ n) x (F x)‖ ≤
      (closedBall p (2 * r n)).indicator (fun _ ↦ 2 * K / r n) x := by
    intro n x
    calc ‖u x * fderiv ℝ (χ n) x (F x)‖ ≤ 1 * (‖fderiv ℝ (χ n) x‖ * 1) := by
          rw [norm_mul]
          exact mul_le_mul (hub x) ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left (hu x) (norm_nonneg _))) (norm_nonneg _) zero_le_one
      _ ≤ _ := by
          rw [one_mul, mul_one]
          exact norm_fderiv_doubledBallCutoff_le (hr n) x
  have hindi : ∀ n, Integrable ((closedBall p (2 * r n)).indicator (fun _ ↦ 2 * K / r n)) :=
    fun n ↦ (ContinuousOn.integrableOn_compact (isCompact_closedBall p _)
      continuousOn_const).integrable_indicator measurableSet_closedBall
  have hint2 : ∀ n, Integrable (fun x ↦ u x * fderiv ℝ (χ n) x (F x)) := by
    intro n
    refine (hindi n).mono' ((hum.mul (((hDχc n).clm_apply hF.continuous).measurable))
      |>.aestronglyMeasurable) (Eventually.of_forall fun x ↦ hbnd n x)
  have hsplit : ∀ n, ∫ x, u x * fieldDivergence b (fun y ↦ χ n y • F y) x =
      (∫ x, u x * (χ n x * fieldDivergence b F x)) + ∫ x, u x * fderiv ℝ (χ n) x (F x) := by
    intro n
    rw [← integral_add (hint1 n) (hint2 n)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [hdiv]
    ring
  have hT1 : Tendsto (fun n ↦ ∫ x, u x * (χ n x * fieldDivergence b F x)) atTop
      (𝓝 (∫ x, u x * fieldDivergence b F x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖fieldDivergence b F x‖)
      (fun n ↦ (hint1 n).aestronglyMeasurable) hdi.norm (fun n ↦ Eventually.of_forall fun x ↦ ?_)
      ?_
    · rw [norm_mul, norm_mul, Real.norm_of_nonneg (doubledBallCutoff_nonneg _ _ _)]
      calc ‖u x‖ * (χ n x * ‖fieldDivergence b F x‖) ≤ 1 * (1 * ‖fieldDivergence b F x‖) :=
            mul_le_mul (hub x) (mul_le_mul_of_nonneg_right (doubledBallCutoff_le_one _ _ _)
              (norm_nonneg _)) (mul_nonneg (doubledBallCutoff_nonneg _ _ _) (norm_nonneg _))
              zero_le_one
        _ = ‖fieldDivergence b F x‖ := by ring
    · have hp0 : volume ({p} : Set (Space d)) = 0 := by
        rw [← closedBall_zero, Measure.addHaar_closedBall volume p le_rfl,
          finrank_euclideanSpace_fin, zero_pow (by omega)]
        simp
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hp0] with x hx
      have hxp : 0 < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
      have hev : ∀ᶠ n in atTop, χ n x = 1 := by
        filter_upwards [hr0.eventually (gt_mem_nhds (half_pos hxp))] with n hn
        exact doubledBallCutoff_eq_one (hr n) (by linarith)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      rw [hn, one_mul]
  have hT2 : Tendsto (fun n ↦ ∫ x, u x * fderiv ℝ (χ n) x (F x)) atTop (𝓝 0) := by
    set vB := volume.real (ball (0 : Space d) 1) with hvB
    have hb2 : ∀ n, ‖∫ x, u x * fderiv ℝ (χ n) x (F x)‖ ≤ 2 * K * 2 ^ d * vB * r n ^ (d - 1) := by
      intro n
      calc ‖∫ x, u x * fderiv ℝ (χ n) x (F x)‖ ≤
            ∫ x, (closedBall p (2 * r n)).indicator (fun _ ↦ 2 * K / r n) x :=
            norm_integral_le_of_norm_le (hindi n) (Eventually.of_forall fun x ↦ hbnd n x)
        _ = volume.real (closedBall p (2 * r n)) * (2 * K / r n) := by
            rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul]
        _ = 2 * K * 2 ^ d * vB * r n ^ (d - 1) := by
            rw [Measure.real, Measure.addHaar_closedBall volume p
              (by positivity : (0 : ℝ) ≤ 2 * r n), finrank_euclideanSpace_fin,
              ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← Measure.real]
            have hrn := (hr n).ne'
            obtain ⟨k, hk⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
            subst hk
            rw [Nat.add_sub_cancel, mul_pow, pow_succ, pow_succ]
            field_simp
            rw [hvB]
            ring
    refine squeeze_zero_norm hb2 ?_
    have h0 : (0 : ℝ) = 2 * K * 2 ^ d * vB * 0 ^ (d - 1) := by
      rw [zero_pow (by omega), mul_zero]
    rw [h0]
    exact (hr0.pow (d - 1)).const_mul _
  have hlim : Tendsto (fun n ↦ ∫ x, u x * fieldDivergence b (fun y ↦ χ n y • F y) x) atTop
      (𝓝 (∫ x, u x * fieldDivergence b F x)) := by
    have h := hT1.add hT2
    rw [add_zero] at h
    exact h.congr fun n ↦ (hsplit n).symm
  exact le_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp
    ((continuous_norm.tendsto _).comp hlim)) hadm


/-! ### 2. Perimeter of affine epigraphs in the plane -/

/-- The point `(s, t)` of the plane. -/
def pt (s t : ℝ) : Space 2 := point (EuclideanSpace.single 0 s) t

theorem pt_zero (s t : ℝ) : pt s t 0 = s := by
  simp [pt, point, Fin.snoc]

theorem pt_one (s t : ℝ) : pt s t 1 = t := by
  simp [pt, point, Fin.snoc]

theorem eq_pt (x : Space 2) : x = pt (x 0) (x 1) := by
  ext i
  fin_cases i
  · exact (pt_zero _ _).symm
  · exact (pt_one _ _).symm

theorem pt_eq_add (s t : ℝ) : pt s t = s • pt 1 0 + t • pt 0 1 := by
  ext i
  fin_cases i
  · simp [pt_zero]
  · simp [pt_one]

theorem continuous_pt {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun s ↦ pt (f s) (g s)) := by
  have h : (fun s ↦ pt (f s) (g s)) = fun s ↦ f s • pt 1 0 + g s • pt 0 1 :=
    funext fun s ↦ pt_eq_add (f s) (g s)
  rw [h]
  exact (hf.smul continuous_const).add (hg.smul continuous_const)

theorem continuous_coord (i : Fin 2) : Continuous (fun x : Space 2 ↦ x i) :=
  (EuclideanSpace.proj i).continuous

theorem abs_coord_le_norm (x : Space 2) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
  apply Real.le_sqrt_of_sq_le
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_abs (x 0), sq_abs (x 1)]

theorem norm_le_abs_add_abs (x : Space 2) : ‖x‖ ≤ |x 0| + |x 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
  apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  nlinarith [abs_nonneg (x 0), abs_nonneg (x 1), sq_abs (x 0), sq_abs (x 1)]

theorem horizontal_apply_zero (x : Space 2) : horizontal x 0 = x 0 := rfl

theorem mem_epigraph_affine (κ c : ℝ) (x : Space 2) :
    x ∈ epigraph (fun y : Space 1 ↦ κ * y 0 + c) ↔ κ * x 0 + c < x 1 := Iff.rfl

theorem graphAreaDensity_affine (κ c : ℝ) (y : Space 1) :
    graphAreaDensity (fun y : Space 1 ↦ κ * y 0 + c) y = Real.sqrt (1 + κ ^ 2) := by
  have hpr : (fun y : Space 1 ↦ y 0) = ⇑(EuclideanSpace.proj (0 : Fin 1) : Space 1 →L[ℝ] ℝ) :=
    funext fun y ↦ by simp
  have h0 : HasFDerivAt (fun y : Space 1 ↦ y 0)
      (EuclideanSpace.proj (0 : Fin 1) : Space 1 →L[ℝ] ℝ) y := by
    rw [hpr]
    exact ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1))
  have hd : HasFDerivAt (fun y : Space 1 ↦ κ * y 0 + c)
      (κ • (EuclideanSpace.proj (0 : Fin 1) : Space 1 →L[ℝ] ℝ)) y :=
    (h0.const_mul κ).add_const c
  have hg : gradient (fun y : Space 1 ↦ κ * y 0 + c) y = κ • EuclideanSpace.single 0 1 := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left, hd.fderiv, real_inner_smul_left, EuclideanSpace.inner_single_left]
    simp
  rw [graphAreaDensity, hg, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs, sq_abs]

/-- **Perimeter of an affine epigraph** in an open subset of the plane. -/
theorem perimeter_epigraph_affine (κ c : ℝ) {U : Set (Space 2)} (hU : IsOpen U) :
    variationalPerimeter (EuclideanSpace.basisFun (Fin 2) ℝ)
        (epigraph (fun y : Space 1 ↦ κ * y 0 + c)) U =
      ENNReal.ofReal (Real.sqrt (1 + κ ^ 2)) * volume {s : ℝ | pt s (κ * s + c) ∈ U} := by
  have hpr : (fun y : Space 1 ↦ y 0) = ⇑(EuclideanSpace.proj (0 : Fin 1) : Space 1 →L[ℝ] ℝ) :=
    funext fun y ↦ by simp
  have h0c : ContDiff ℝ 1 (fun y : Space 1 ↦ y 0) := by
    rw [hpr]
    exact ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1))
  have hb : ContDiff ℝ 1 (fun y : Space 1 ↦ κ * y 0 + c) :=
    (contDiff_const.mul h0c).add contDiff_const
  rw [graph_perimeter_eq_area (EuclideanSpace.basisFun (Fin 2) ℝ) hb hU]
  simp_rw [graphAreaDensity_affine]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  congr 1
  have hmp : MeasurePreserving (fun y : Space 1 ↦ y 0) :=
    (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))
  have hset : {y : Space 1 | point y (κ * y 0 + c) ∈ U} =
      (fun y : Space 1 ↦ y 0) ⁻¹' {s : ℝ | pt s (κ * s + c) ∈ U} := by
    ext y
    have hy : y = EuclideanSpace.single 0 (y 0) := by
      ext i
      fin_cases i
      simp
    simp only [mem_ofPred_eq, mem_preimage]
    conv_lhs => rw [hy]
    rfl
  rw [hset, hmp.measure_preimage]
  have hcont : Continuous (fun s : ℝ ↦ pt s (κ * s + c)) :=
    continuous_pt continuous_id ((continuous_const.mul continuous_id).add continuous_const)
  exact (hU.preimage hcont).measurableSet.nullMeasurableSet

theorem le_perimeter_epigraph_affine (κ c : ℝ) {U : Set (Space 2)} (hU : IsOpen U) {α β : ℝ}
    (hsub : ∀ s ∈ Ioo α β, pt s (κ * s + c) ∈ U) :
    ENNReal.ofReal (Real.sqrt (1 + κ ^ 2) * (β - α)) ≤
      variationalPerimeter (EuclideanSpace.basisFun (Fin 2) ℝ)
        (epigraph (fun y : Space 1 ↦ κ * y 0 + c)) U := by
  rw [perimeter_epigraph_affine κ c hU, ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ← Real.volume_Ioo]
  gcongr
  exact fun s hs ↦ hsub s hs

theorem perimeter_epigraph_affine_le (κ c : ℝ) {U : Set (Space 2)} (hU : IsOpen U) {α β : ℝ}
    (hsub : ∀ s, pt s (κ * s + c) ∈ U → s ∈ Ioo α β) :
    variationalPerimeter (EuclideanSpace.basisFun (Fin 2) ℝ)
        (epigraph (fun y : Space 1 ↦ κ * y 0 + c)) U ≤
      ENNReal.ofReal (Real.sqrt (1 + κ ^ 2) * (β - α)) := by
  rw [perimeter_epigraph_affine κ c hU, ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ← Real.volume_Ioo]
  gcongr
  exact fun s hs ↦ hsub s hs


/-! ### 3. The chord contradiction -/

theorem pt_zero_zero : pt 0 0 = 0 := by
  ext i
  fin_cases i
  · simp [pt_zero]
  · simp [pt_one]

/-- **The chord argument.** A minimizing cone in the plane cannot coincide, on a sector
`{κ' |x₁| < x₂}`, with the narrower convex sector `{κ |x₁| < x₂}` (`0 < κ' < κ`). -/
theorem chord_false {E : Set (Space 2)} (hE : IsMinimizingCone E) {κ κ' : ℝ} (hκ' : 0 < κ')
    (hκκ' : κ' < κ) (hES : ∀ᵐ x ∂volume, κ' * |x 0| < x 1 → (x ∈ E ↔ κ * |x 0| < x 1)) :
    False := by
  set b := EuclideanSpace.basisFun (Fin 2) ℝ with hb
  have hκ : 0 < κ := hκ'.trans hκκ'
  set s₀ := Real.sqrt (1 + κ ^ 2) with hs₀
  have hs₀1 : 1 < s₀ := (Real.lt_sqrt zero_le_one).mpr (by nlinarith [sq_pos_of_pos hκ])
  have hs₀neg : Real.sqrt (1 + (-κ) ^ 2) = s₀ := by rw [neg_sq]
  set C := minimizerPerimeterUpperConst 1 with hCdef
  have hC : 0 < C := minimizerPerimeterUpperConst_pos 1
  set ρ := min (1 / 2) ((s₀ - 1) / (κ * C)) with hρdef
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos (by linarith) (mul_pos hκ hC))
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have hCρ : C * ρ ≤ (s₀ - 1) / κ := by
    have h := min_le_right (1 / 2 : ℝ) ((s₀ - 1) / (κ * C))
    calc C * ρ ≤ C * ((s₀ - 1) / (κ * C)) := mul_le_mul_of_nonneg_left h hC.le
      _ = (s₀ - 1) / κ := by field_simp
  have hc0 := continuous_coord 0
  have hc1 := continuous_coord 1
  have hcw' : Continuous (fun x : Space 2 ↦ κ' * |x 0|) := continuous_const.mul hc0.abs
  have hcw : Continuous (fun x : Space 2 ↦ κ * |x 0|) := continuous_const.mul hc0.abs
  have hcg : Continuous (fun x : Space 2 ↦ max (κ * |x 0|) 1) := hcw.max continuous_const
  -- the sets
  set W₂ : Set (Space 2) := {x | κ' * |x 0| < x 1 ∧ x 1 < 2} with hW₂
  set Δ : Set (Space 2) := {x | κ * |x 0| < x 1 ∧ x 1 < 1} with hΔ
  set D := E \ Δ with hD
  set N := W₂ ∪ ball (0 : Space 2) ρ with hN
  set K : Set (Space 2) := {x | κ * |x 0| ≤ x 1 ∧ x 1 ≤ 1} with hK
  have hW₂o : IsOpen W₂ := (isOpen_lt hcw' hc1).inter (isOpen_lt hc1 continuous_const)
  have hΔo : IsOpen Δ := (isOpen_lt hcw hc1).inter (isOpen_lt hc1 continuous_const)
  have hNo : IsOpen N := hW₂o.union isOpen_ball
  have hDm : MeasurableSet D := hE.measurableSet.diff hΔo.measurableSet
  have hmemW : ∀ x : Space 2, x ≠ 0 → κ * |x 0| ≤ x 1 → κ' * |x 0| < x 1 := by
    intro x hx0 hx
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := fun h1 ↦ hx0 (by rw [eq_pt x, h0, h1, pt_zero_zero])
      rw [h0, abs_zero, mul_zero] at hx ⊢
      exact lt_of_le_of_ne hx (Ne.symm h1)
    · have hpos : 0 < |x 0| := abs_pos.mpr h0
      nlinarith
  -- minimality against the cut competitor
  have hKN : K ⊆ N := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inr (by rw [hx0]; exact mem_ball_self hρ)
    · exact Or.inl ⟨hmemW x hx0 hx.1, by linarith [hx.2]⟩
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Space 2) (1 / κ + 1)).of_isClosed_subset
      ((isClosed_le hcw hc1).inter (isClosed_le hc1 continuous_const)) fun x hx ↦ ?_
    rw [mem_closedBall, dist_zero_right]
    have h1 : 0 ≤ x 1 := le_trans (by positivity) hx.1
    have h2 : |x 0| ≤ 1 / κ := by
      rw [le_div_iff₀ hκ]
      nlinarith [hx.1, hx.2]
    calc ‖x‖ ≤ |x 0| + |x 1| := norm_le_abs_add_abs x
      _ ≤ 1 / κ + 1 := add_le_add h2 (by rw [abs_of_nonneg h1]; exact hx.2)
  have hED : ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D) := by
    refine Eventually.of_forall fun x hxK ↦ ?_
    have hxΔ : x ∉ Δ := fun h ↦ hxK ⟨h.1.le, h.2.le⟩
    exact ⟨fun h ↦ ⟨h, hxΔ⟩, fun h ↦ h.1⟩
  have hmin := hE.minimizer.minimizes N D K hNo (subset_univ _) hDm hKc hKN hED
  -- the perimeter measure of `E`
  have hPE : ∀ n : ℕ, variationalPerimeter b E (ball 0 ((n : ℝ) + 1)) ≠ ⊤ := fun n ↦
    hE.minimizer.perimeter_ball_ne_top 0 _ (by positivity) (subset_univ _)
  set μE := perimeterRadonMeasure b hE.measurableSet hPE with hμEdef
  have hμE : ∀ U, IsOpen U → μE U = variationalPerimeter b E U := fun U hU ↦
    perimeterRadonMeasure_apply_open b hE.measurableSet hPE hU
  -- lower bound: the two segments of `E`
  set Rp : Set (Space 2) := {x | κ' * |x 0| < x 1 ∧ x 1 < 2 ∧ 0 < x 0} with hRp
  set Rm : Set (Space 2) := {x | κ' * |x 0| < x 1 ∧ x 1 < 2 ∧ x 0 < 0} with hRm
  have hRpo : IsOpen Rp :=
    (isOpen_lt hcw' hc1).inter
      ((isOpen_lt hc1 continuous_const).inter (isOpen_lt continuous_const hc0))
  have hRmo : IsOpen Rm :=
    (isOpen_lt hcw' hc1).inter
      ((isOpen_lt hc1 continuous_const).inter (isOpen_lt hc0 continuous_const))
  have hEp : variationalPerimeter b E Rp =
      variationalPerimeter b (epigraph (fun y : Space 1 ↦ κ * y 0 + 0)) Rp := by
    apply variationalPerimeter_congr_ae_on b
    filter_upwards [hES] with x hx hxR
    rw [hx hxR.1, mem_epigraph_affine, abs_of_pos hxR.2.2, add_zero]
  have hEm : variationalPerimeter b E Rm =
      variationalPerimeter b (epigraph (fun y : Space 1 ↦ (-κ) * y 0 + 0)) Rm := by
    apply variationalPerimeter_congr_ae_on b
    filter_upwards [hES] with x hx hxR
    rw [hx hxR.1, mem_epigraph_affine, abs_of_neg hxR.2.2, add_zero, neg_mul, mul_neg]
  have hlp : ENNReal.ofReal (s₀ * (2 / κ - 0)) ≤ variationalPerimeter b E Rp := by
    rw [hEp]
    refine le_perimeter_epigraph_affine κ 0 hRpo fun t ht ↦ ?_
    simp only [hRp, mem_ofPred_eq, pt_zero, pt_one, add_zero]
    refine ⟨?_, ?_, ht.1⟩
    · rw [abs_of_pos ht.1]
      exact mul_lt_mul_of_pos_right hκκ' ht.1
    · have := ht.2
      rw [lt_div_iff₀ hκ] at this
      linarith
  have hlm : ENNReal.ofReal (s₀ * (0 - -(2 / κ))) ≤ variationalPerimeter b E Rm := by
    rw [hEm, ← hs₀neg]
    refine le_perimeter_epigraph_affine (-κ) 0 hRmo fun t ht ↦ ?_
    simp only [hRm, mem_ofPred_eq, pt_zero, pt_one, add_zero]
    refine ⟨?_, ?_, ht.2⟩
    · rw [abs_of_neg ht.2]
      nlinarith [ht.2]
    · have h := mul_lt_mul_of_pos_left ht.1 hκ
      have e : κ * -(2 / κ) = -2 := by field_simp
      rw [e] at h
      linarith
  have hlow : ENNReal.ofReal (s₀ * (2 / κ - 0)) + ENNReal.ofReal (s₀ * (0 - -(2 / κ))) ≤
      variationalPerimeter b E N := by
    have hdisj : Disjoint Rp Rm := by
      rw [disjoint_left]
      intro x hp hm
      linarith [hp.2.2, hm.2.2]
    have hsub : Rp ∪ Rm ⊆ N := by
      rintro x (hx | hx)
      · exact Or.inl ⟨hx.1, hx.2.1⟩
      · exact Or.inl ⟨hx.1, hx.2.1⟩
    calc ENNReal.ofReal (s₀ * (2 / κ - 0)) + ENNReal.ofReal (s₀ * (0 - -(2 / κ)))
        ≤ variationalPerimeter b E Rp + variationalPerimeter b E Rm := add_le_add hlp hlm
      _ = μE (Rp ∪ Rm) := by rw [measure_union hdisj hRmo.measurableSet, hμE _ hRpo, hμE _ hRmo]
      _ ≤ μE N := measure_mono hsub
      _ = variationalPerimeter b E N := hμE _ hNo
  -- upper bound away from the vertex
  set c₁ := pt (1 / κ) 1 with hc₁
  set c₂ := pt (-(1 / κ)) 1 with hc₂
  set A₁ : Set (Space 2) := {x | κ' * |x 0| < x 1 ∧ x 1 < 2 ∧ max (κ * |x 0|) 1 < x 1} with hA₁
  set A₂ : Set (Space 2) := {x | κ' * |x 0| < x 1 ∧ x 1 < 2 ∧ x 1 < max (κ * |x 0|) 1} with hA₂
  set A₃ : Set (Space 2) := {x | κ' * |x 0| < x 1 ∧ x 1 < 2 ∧ 1 / κ < x 0} with hA₃
  set A₄ : Set (Space 2) := {x | κ' * |x 0| < x 1 ∧ x 1 < 2 ∧ |x 0| < 1 / κ} with hA₄
  set A₅ : Set (Space 2) := {x | κ' * |x 0| < x 1 ∧ x 1 < 2 ∧ x 0 < -(1 / κ)} with hA₅
  have hbase : IsOpen {x : Space 2 | κ' * |x 0| < x 1 ∧ x 1 < 2} := hW₂o
  have hA₁o : IsOpen A₁ :=
    (isOpen_lt hcw' hc1).inter ((isOpen_lt hc1 continuous_const).inter (isOpen_lt hcg hc1))
  have hA₂o : IsOpen A₂ :=
    (isOpen_lt hcw' hc1).inter ((isOpen_lt hc1 continuous_const).inter (isOpen_lt hc1 hcg))
  have hA₃o : IsOpen A₃ :=
    (isOpen_lt hcw' hc1).inter
      ((isOpen_lt hc1 continuous_const).inter (isOpen_lt continuous_const hc0))
  have hA₄o : IsOpen A₄ :=
    (isOpen_lt hcw' hc1).inter ((isOpen_lt hc1 continuous_const).inter
      (isOpen_lt hc0.abs continuous_const))
  have hA₅o : IsOpen A₅ :=
    (isOpen_lt hcw' hc1).inter
      ((isOpen_lt hc1 continuous_const).inter (isOpen_lt hc0 continuous_const))
  have hcover : (W₂ \ {c₁}) \ {c₂} ⊆ A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅ := by
    rintro x ⟨⟨hxW, hx1⟩, hx2⟩
    rcases lt_trichotomy (x 1) (max (κ * |x 0|) 1) with h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hxW.1, hxW.2, h⟩)))
    · rcases lt_trichotomy (x 0) (1 / κ) with h0 | h0 | h0
      · rcases lt_trichotomy (x 0) (-(1 / κ)) with h0' | h0' | h0'
        · exact Or.inr ⟨hxW.1, hxW.2, h0'⟩
        · exfalso
          apply hx2
          rw [mem_singleton_iff, eq_pt x, h0', hc₂]
          congr 1
          rw [h, h0', abs_neg, abs_of_pos (by positivity), mul_one_div_cancel hκ.ne', max_self]
        · exact Or.inl (Or.inr ⟨hxW.1, hxW.2, abs_lt.mpr ⟨h0', h0⟩⟩)
      · exfalso
        apply hx1
        rw [mem_singleton_iff, eq_pt x, h0, hc₁]
        congr 1
        rw [h, h0, abs_of_pos (by positivity), mul_one_div_cancel hκ.ne', max_self]
      · exact Or.inl (Or.inl (Or.inr ⟨hxW.1, hxW.2, h0⟩))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hxW.1, hxW.2, h⟩)))
  have hP1 : variationalPerimeter b D A₁ = 0 := by
    rw [variationalPerimeter_congr_ae_on b (D := univ), variationalPerimeter_univ]
    filter_upwards [hES] with x hx hxA
    simp only [mem_univ, iff_true]
    have hE' : x ∈ E := (hx hxA.1).mpr (lt_of_le_of_lt (le_max_left _ _) hxA.2.2)
    exact ⟨hE', fun hΔx ↦ by linarith [hΔx.2, le_max_right (κ * |x 0|) 1, hxA.2.2]⟩
  have hP2 : variationalPerimeter b D A₂ = 0 := by
    rw [variationalPerimeter_congr_ae_on b (D := ∅), variationalPerimeter_empty]
    filter_upwards [hES] with x hx hxA
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨hxE, hxΔ⟩
    have h1 := (hx hxA.1).mp hxE
    apply hxΔ
    refine ⟨h1, ?_⟩
    by_contra h2
    rw [not_lt] at h2
    exact absurd (max_le h1.le h2) (not_le.mpr hxA.2.2)
  have hP3 : variationalPerimeter b D A₃ ≤ ENNReal.ofReal (s₀ * (2 / κ - 1 / κ)) := by
    rw [variationalPerimeter_congr_ae_on b (D := epigraph (fun y : Space 1 ↦ κ * y 0 + 0))]
    · refine perimeter_epigraph_affine_le κ 0 hA₃o fun t ht ↦ ?_
      simp only [hA₃, mem_ofPred_eq, pt_zero, pt_one, add_zero] at ht
      refine ⟨ht.2.2, ?_⟩
      rw [lt_div_iff₀ hκ]
      linarith [ht.2.1]
    · filter_upwards [hES] with x hx hxA
      have hx0 : 0 < x 0 := lt_trans (by positivity) hxA.2.2
      have hk1 : 1 < κ * x 0 := by
        have := hxA.2.2
        rw [div_lt_iff₀ hκ] at this
        linarith
      rw [mem_epigraph_affine, add_zero]
      constructor
      · rintro ⟨hxE, -⟩
        have := (hx hxA.1).mp hxE
        rwa [abs_of_pos hx0] at this
      · intro h
        refine ⟨(hx hxA.1).mpr (by rwa [abs_of_pos hx0]), fun hΔx ↦ by linarith [hΔx.2]⟩
  have hnull1 : ∀ᵐ x ∂(volume : Measure (Space 2)), x 1 ≠ 1 := by
    have hz :
        volume {x : Space 2 | inner ℝ (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x = 0} = 0 :=
      volume_orthogonal_hyperplane_eq_zero (by simp)
    have hshift : {x : Space 2 | x 1 = 1} =
        (fun x ↦ x + pt 0 (-1)) ⁻¹'
          {x : Space 2 | inner ℝ (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x = 0} := by
      ext x
      simp [EuclideanSpace.inner_single_left, pt_one]
      constructor <;> intro h <;> linarith
    have h0 : volume {x : Space 2 | x 1 = 1} = 0 := by
      rw [hshift, measure_preimage_add_right]
      exact hz
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
    exact hx
  have hP4 : variationalPerimeter b D A₄ ≤ ENNReal.ofReal (1 * (1 / κ - -(1 / κ))) := by
    rw [variationalPerimeter_congr_ae_on b (D := epigraph (fun y : Space 1 ↦ 0 * y 0 + 1))]
    · have h := perimeter_epigraph_affine_le 0 1 hA₄o (α := -(1 / κ)) (β := 1 / κ) fun t ht ↦ by
        simp only [hA₄, mem_ofPred_eq, pt_zero, pt_one, zero_mul, zero_add] at ht
        exact abs_lt.mp ht.2.2
      simpa using h
    · filter_upwards [hES, hnull1] with x hx hx1 hxA
      have hk : κ * |x 0| < 1 := by
        have := hxA.2.2
        rw [lt_div_iff₀ hκ] at this
        linarith
      rw [mem_epigraph_affine, zero_mul, zero_add]
      constructor
      · rintro ⟨hxE, hxΔ⟩
        have h1 := (hx hxA.1).mp hxE
        by_contra h2
        rw [not_lt] at h2
        exact hxΔ ⟨h1, lt_of_le_of_ne h2 hx1⟩
      · intro h
        exact ⟨(hx hxA.1).mpr (by linarith), fun hΔx ↦ by linarith [hΔx.2]⟩
  have hP5 : variationalPerimeter b D A₅ ≤ ENNReal.ofReal (s₀ * (-(1 / κ) - -(2 / κ))) := by
    rw [variationalPerimeter_congr_ae_on b (D := epigraph (fun y : Space 1 ↦ (-κ) * y 0 + 0)),
      ← hs₀neg]
    · refine perimeter_epigraph_affine_le (-κ) 0 hA₅o fun t ht ↦ ?_
      simp only [hA₅, mem_ofPred_eq, pt_zero, pt_one, add_zero] at ht
      refine ⟨?_, ht.2.2⟩
      have h := ht.2.1
      have e : κ * (2 / κ) = 2 := by field_simp
      by_contra hc
      rw [not_lt] at hc
      have := mul_le_mul_of_nonneg_left hc hκ.le
      rw [mul_neg, e] at this
      linarith
    · filter_upwards [hES] with x hx hxA
      have hx0 : x 0 < 0 := lt_trans hxA.2.2 (by
        have : (0 : ℝ) < 1 / κ := by positivity
        linarith)
      have hk1 : 1 < -κ * x 0 := by
        have := hxA.2.2
        rw [lt_neg, div_lt_iff₀ hκ] at this
        linarith
      rw [mem_epigraph_affine, add_zero]
      constructor
      · rintro ⟨hxE, -⟩
        have := (hx hxA.1).mp hxE
        rwa [abs_of_neg hx0, mul_neg, ← neg_mul] at this
      · intro h
        refine ⟨(hx hxA.1).mpr (by rwa [abs_of_neg hx0, mul_neg, ← neg_mul]),
          fun hΔx ↦ by linarith [hΔx.2]⟩
  have hW : variationalPerimeter b D W₂ ≤ ENNReal.ofReal (s₀ * (2 / κ - 1 / κ)) +
      ENNReal.ofReal (1 * (1 / κ - -(1 / κ))) + ENNReal.ofReal (s₀ * (-(1 / κ) - -(2 / κ))) := by
    calc variationalPerimeter b D W₂
        ≤ variationalPerimeter b D ((W₂ \ {c₁}) \ {c₂}) :=
          (variationalPerimeter_le_diff_singleton le_rfl b hDm W₂ c₁).trans
            (variationalPerimeter_le_diff_singleton le_rfl b hDm _ c₂)
      _ ≤ variationalPerimeter b D (A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅) := variationalPerimeter_mono b D hcover
      _ ≤ variationalPerimeter b D (A₁ ∪ A₂ ∪ A₃ ∪ A₄) + variationalPerimeter b D A₅ :=
          variationalPerimeter_union_le_add b hDm
            (((hA₁o.union hA₂o).union hA₃o).union hA₄o) hA₅o
      _ ≤ (variationalPerimeter b D (A₁ ∪ A₂ ∪ A₃) + variationalPerimeter b D A₄) +
            variationalPerimeter b D A₅ := by
          gcongr
          exact variationalPerimeter_union_le_add b hDm ((hA₁o.union hA₂o).union hA₃o) hA₄o
      _ ≤ ((variationalPerimeter b D (A₁ ∪ A₂) + variationalPerimeter b D A₃) +
            variationalPerimeter b D A₄) + variationalPerimeter b D A₅ := by
          gcongr
          exact variationalPerimeter_union_le_add b hDm (hA₁o.union hA₂o) hA₃o
      _ ≤ (((variationalPerimeter b D A₁ + variationalPerimeter b D A₂) +
            variationalPerimeter b D A₃) + variationalPerimeter b D A₄) +
              variationalPerimeter b D A₅ := by
          gcongr
          exact variationalPerimeter_union_le_add b hDm hA₁o hA₂o
      _ ≤ _ := by
          rw [hP1, hP2, zero_add, zero_add]
          gcongr
  -- upper bound near the vertex
  set B₁ : Set (Space 2) := {x | ‖x‖ < ρ ∧ x 1 < κ * |x 0|} with hB₁
  set B₂ : Set (Space 2) := {x | ‖x‖ < ρ ∧ κ' * |x 0| < x 1} with hB₂
  have hB₁o : IsOpen B₁ := (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt hc1 hcw)
  have hB₂o : IsOpen B₂ := (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt hcw' hc1)
  have hball : variationalPerimeter b D (ball 0 ρ) ≤ ENNReal.ofReal (C * ρ ^ 1) := by
    have hcov : ball (0 : Space 2) ρ \ {0} ⊆ B₁ ∪ B₂ := by
      rintro x ⟨hxb, hx0⟩
      rw [mem_ball, dist_zero_right] at hxb
      by_cases h : x 1 < κ * |x 0|
      · exact Or.inl ⟨hxb, h⟩
      · exact Or.inr ⟨hxb, hmemW x hx0 (not_lt.mp h)⟩
    have hD1 : variationalPerimeter b D B₁ = variationalPerimeter b E B₁ := by
      apply variationalPerimeter_congr_ae_on b
      refine Eventually.of_forall fun x hxB ↦ ?_
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun hΔx ↦ by linarith [hΔx.1, hxB.2]⟩⟩
    have hD2 : variationalPerimeter b D B₂ = 0 := by
      rw [variationalPerimeter_congr_ae_on b (D := ∅), variationalPerimeter_empty]
      filter_upwards [hES] with x hx hxB
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨hxE, hxΔ⟩
      have h1 := (hx hxB.2).mp hxE
      have h2 : x 1 < 1 := by
        have := (le_abs_self (x 1)).trans (abs_coord_le_norm x 1)
        linarith [hxB.1]
      exact hxΔ ⟨h1, h2⟩
    calc variationalPerimeter b D (ball 0 ρ) ≤ variationalPerimeter b D (ball 0 ρ \ {0}) :=
          variationalPerimeter_le_diff_singleton le_rfl b hDm _ 0
      _ ≤ variationalPerimeter b D (B₁ ∪ B₂) := variationalPerimeter_mono b D hcov
      _ ≤ variationalPerimeter b D B₁ + variationalPerimeter b D B₂ :=
          variationalPerimeter_union_le_add b hDm hB₁o hB₂o
      _ = variationalPerimeter b E B₁ := by rw [hD1, hD2, add_zero]
      _ ≤ variationalPerimeter b E (ball 0 ρ) :=
          variationalPerimeter_mono b E fun x hx ↦ by
            rw [mem_ball, dist_zero_right]
            exact hx.1
      _ ≤ ENNReal.ofReal (C * ρ ^ 1) := hE.minimizer.variationalPerimeter_ball_le hρ (subset_univ _)
  have hup : variationalPerimeter b D N ≤ (ENNReal.ofReal (s₀ * (2 / κ - 1 / κ)) +
      ENNReal.ofReal (1 * (1 / κ - -(1 / κ))) + ENNReal.ofReal (s₀ * (-(1 / κ) - -(2 / κ)))) +
        ENNReal.ofReal (C * ρ ^ 1) :=
    (variationalPerimeter_union_le_add b hDm hW₂o isOpen_ball).trans (add_le_add hW hball)
  -- the contradiction
  have hall := hlow.trans (hmin.trans hup)
  have hk1 : (0 : ℝ) < 1 / κ := by positivity
  have e21 : 2 / κ = 2 * (1 / κ) := by ring
  have hs0 : 0 ≤ s₀ := Real.sqrt_nonneg _
  have n1 : 0 ≤ s₀ * (2 / κ - 0) := mul_nonneg hs0 (by linarith [e21, hk1])
  have n2 : 0 ≤ s₀ * (0 - -(2 / κ)) := mul_nonneg hs0 (by linarith [e21, hk1])
  have n3 : 0 ≤ s₀ * (2 / κ - 1 / κ) := mul_nonneg hs0 (by linarith [e21, hk1])
  have n4 : (0 : ℝ) ≤ 1 * (1 / κ - -(1 / κ)) := by linarith
  have n5 : 0 ≤ s₀ * (-(1 / κ) - -(2 / κ)) := mul_nonneg hs0 (by linarith [e21, hk1])
  have n6 : 0 ≤ C * ρ ^ 1 := by rw [pow_one]; exact (mul_pos hC hρ).le
  rw [← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add n3 n4,
    ← ENNReal.ofReal_add (add_nonneg n3 n4) n5,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg n3 n4) n5) n6,
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (add_nonneg (add_nonneg n3 n4) n5) n6)] at hall
  have h2 : 2 * (s₀ - 1) / κ ≤ C * ρ := by
    have e : s₀ * (2 / κ - 0) + s₀ * (0 - -(2 / κ)) = 4 * s₀ / κ := by ring
    have e2 : s₀ * (2 / κ - 1 / κ) + 1 * (1 / κ - -(1 / κ)) + s₀ * (-(1 / κ) - -(2 / κ)) +
        C * ρ ^ 1 = 2 * s₀ / κ + 2 / κ + C * ρ := by ring
    rw [e, e2] at hall
    have : 2 * (s₀ - 1) / κ = 4 * s₀ / κ - (2 * s₀ / κ + 2 / κ) := by ring
    linarith
  have h3 : (s₀ - 1) / κ < 2 * (s₀ - 1) / κ := by
    have : 0 < (s₀ - 1) / κ := div_pos (by linarith) hκ
    linarith [show 2 * (s₀ - 1) / κ = 2 * ((s₀ - 1) / κ) by ring]
  linarith

end Planar

end SerrinEpigraph
