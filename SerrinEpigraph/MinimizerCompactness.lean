module

public import SerrinEpigraph.LocalPerimeterMinimizer
public import SerrinEpigraph.BVBallGluing
public import SerrinEpigraph.PerimeterLowerSemicontinuity
public import SerrinEpigraph.BVTranslation
public import SerrinEpigraph.MollificationIntegralError
public import SerrinEpigraph.PlaneTiltBVCompactness
public import SerrinEpigraph.GlobalPrimitiveLimit
public import SerrinEpigraph.GlobalPhaseSet
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Compactness and continuity-ball perimeter convergence for local perimeter minimizers (BV8)

This module proves the compactness and convergence package for `IsLocalPerimeterMinimizer`
(BV8 in `docs/rigidity-proof/bv-minimizers.md`):
- self-contained dimensional ball-perimeter upper bounds `O(r ^ (d - 1))` for any local
  perimeter minimizer via ball-deletion gluing (`IsLocalPerimeterMinimizer.perimeter_ball_le`);
- binary open subadditivity of variational perimeter (`variationalPerimeter_union_le_add`) and
  local compact-perturbation localization (`perimeter_comparison_localize_of_compact_perturbation`);
- stability of `IsLocalPerimeterMinimizer` under `L¹_loc` indicator convergence via summable
  subsequence extraction, monotone derivative integration, and spherical ball gluing without
  spherical coarea or boundary rectifiability;
- equivalence of zero sphere mass and right-continuity of ball perimeters, together with
  continuity-ball perimeter convergence (BV8, `tendsto_variationalPerimeter_ball_of_sphere_zero`);
- `L¹_loc` subsequence compactness for sequences of local perimeter minimizers (including
  blowup families that are only eventually minimal on exhausting balls).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology CompactlySupported ENNReal BoundedContinuousFunction

namespace SerrinEpigraph

/-! ### 1. Self-contained local ball perimeter bound for local perimeter minimizers -/

/-- Real volume of a Euclidean ball of positive radius in terms of the unit-ball constant. -/
theorem volume_real_ball_eq {d : ℕ} (x₀ : Space d) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x₀ r) = volume.real (ball (0 : Space d) 1) * r ^ d := by
  change (volume (ball x₀ r)).toReal = (volume (ball (0 : Space d) 1)).toReal * r ^ d
  rw [volume.addHaar_ball_of_pos x₀ hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  simp only [Space, finrank_euclideanSpace_fin]
  ring

/-- At any positive radius where `ρ ↦ volume.real (F ∩ ball x₀ ρ)` is differentiable, its radial
derivative is bounded by `d * ω_d * ρ ^ (d - 1)`. -/
theorem volume_inter_ball_deriv_le {d : ℕ} {F : Set (Space d)}
    (hF : MeasurableSet F) (x₀ : Space d) {ρ d' : ℝ} (hρ : 0 < ρ)
    (hderiv : HasDerivAt (fun t ↦ volume.real (F ∩ ball x₀ t)) d' ρ) :
    d' ≤ (d : ℝ) * volume.real (ball (0 : Space d) 1) * ρ ^ (d - 1) := by
  let V : ℝ → ℝ := fun t ↦ volume.real (F ∩ ball x₀ t)
  let ω : ℝ := volume.real (ball (0 : Space d) 1)
  let W : ℝ → ℝ := fun t ↦ ω * t ^ d
  have hW_deriv : HasDerivAt W ((d : ℝ) * ω * ρ ^ (d - 1)) ρ := by
    have hp := (hasDerivAt_pow d ρ).const_mul ω
    convert hp using 1
    ring
  have hV_slope : Tendsto (slope V ρ) (𝓝[>] ρ) (𝓝 d') := by
    have h1 := hderiv.hasDerivWithinAt (s := Ioi ρ)
    rw [hasDerivWithinAt_iff_tendsto_slope] at h1
    have hdiff : Ioi ρ \ {ρ} = Ioi ρ := by
      ext t
      simp only [Set.mem_sdiff, mem_Ioi, mem_singleton_iff, and_iff_left_iff_imp]
      exact fun h ↦ h.ne'
    rwa [hdiff] at h1
  have hW_slope : Tendsto (slope W ρ) (𝓝[>] ρ) (𝓝 ((d : ℝ) * ω * ρ ^ (d - 1))) := by
    have h1 := hW_deriv.hasDerivWithinAt (s := Ioi ρ)
    rw [hasDerivWithinAt_iff_tendsto_slope] at h1
    have hdiff : Ioi ρ \ {ρ} = Ioi ρ := by
      ext t
      simp only [Set.mem_sdiff, mem_Ioi, mem_singleton_iff, and_iff_left_iff_imp]
      exact fun h ↦ h.ne'
    rwa [hdiff] at h1
  refine le_of_tendsto_of_tendsto hV_slope hW_slope ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : ρ < t)
  have htpos : 0 < t := hρ.trans ht
  have hdiff_le : V t - V ρ ≤ W t - W ρ := by
    have hsubF : F ∩ ball x₀ ρ ⊆ F ∩ ball x₀ t :=
      inter_subset_inter_right F (ball_subset_ball ht.le)
    have hVdiff : V t - V ρ = volume.real ((F ∩ ball x₀ t) \ (F ∩ ball x₀ ρ)) :=
      (measureReal_sdiff hsubF (hF.inter measurableSet_ball)).symm
    have hWdiff : W t - W ρ = volume.real (ball x₀ t \ ball x₀ ρ) := by
      dsimp [W, ω]
      rw [← volume_real_ball_eq x₀ htpos, ← volume_real_ball_eq x₀ hρ,
        ← measureReal_sdiff (ball_subset_ball ht.le) measurableSet_ball]
    rw [hVdiff, hWdiff]
    refine measureReal_mono ?_ ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
    intro x hx
    exact ⟨hx.1.2, fun hxb ↦ hx.2 ⟨hx.1.1, hxb⟩⟩
  rw [slope_def_field, slope_def_field]
  exact div_le_div_of_nonneg_right hdiff_le (sub_pos.mpr ht).le

/-- Universal dimensional upper bound on `variationalPerimeter b F (ball x₀ r)` for any local
perimeter minimizer `F` on `closedBall x₀ r ⊆ Ω`. -/
theorem IsLocalPerimeterMinimizer.perimeter_ball_le {d : ℕ} (hd : 1 ≤ d)
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {F Ω : Set (Space d)}
    (hmin : IsLocalPerimeterMinimizer b F Ω) {x₀ : Space d} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω) :
    variationalPerimeter b F (ball x₀ r) ≤
      ENNReal.ofReal (ballGluingConstant * (d : ℝ) *
        volume.real (ball (0 : Space d) 1) * r ^ (d - 1)) := by
  obtain ⟨δ, μ, -, hδ, hcb, hμ_fin, -, hμ_open, -, -, -⟩ :=
    hmin.exists_ball_radon_measure hr hsub
  let _ : IsFiniteMeasure μ := hμ_fin
  let Ω₀ : Set (Space d) := ball x₀ (r + δ)
  let V : ℝ → ℝ := fun ρ ↦ volume.real (F ∩ ball x₀ ρ)
  let C : ℝ := ballGluingConstant * (d : ℝ) * volume.real (ball (0 : Space d) 1)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg ballGluingConstant_pos.le (Nat.cast_nonneg d)) measureReal_nonneg
  have hV_mono : Monotone V := monotone_volume_real_inter_ball F x₀
  have hstep : ∀ t ∈ Ioo r (r + δ),
      variationalPerimeter b F (ball x₀ r) ≤ ENNReal.ofReal (C * t ^ (d - 1)) := by
    intro t ht
    have hae : ∀ᵐ s : ℝ ∂volume.restrict (Ioo r t), HasDerivAt V (deriv V s) s := by
      filter_upwards [ae_restrict_of_ae hV_mono.ae_hasDerivAt] with s hs
      exact hs.deriv ▸ hs
    have hne_zero : volume.restrict (Ioo r t) ≠ 0 := by
      intro h0
      have hpos : (volume.restrict (Ioo r t)) univ ≠ 0 := by
        rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
        exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht.1)).ne'
      exact hpos (by simp [h0])
    obtain ⟨s, hdV, hs_mem⟩ :=
      @Filter.Eventually.exists _ _ _ (ae_neBot.mpr hne_zero)
        (hae.and (ae_restrict_mem measurableSet_Ioo))
    have hs_pos : 0 < s := hr.trans hs_mem.1
    have hs_sub : closedBall x₀ s ⊆ Ω₀ := closedBall_subset_ball (hs_mem.2.trans ht.2)
    have hmin_s : variationalPerimeter b F Ω₀ ≤ variationalPerimeter b (F \ ball x₀ s) Ω₀ := by
      refine hmin.minimizes Ω₀ (F \ ball x₀ s) (closedBall x₀ s) isOpen_ball
        (ball_subset_closedBall.trans hcb) (hmin.measurableSet.diff measurableSet_ball)
        (isCompact_closedBall x₀ s) hs_sub ?_
      refine Eventually.of_forall fun x hx ↦ ?_
      have hxnot : x ∉ ball x₀ s := fun hb ↦ hx (ball_subset_closedBall hb)
      simp [hxnot]
    have hclosed_le := perimeter_closedBall_le_of_sdiff_ball_comparison hd b hmin.measurableSet
      isOpen_ball μ hμ_open hs_pos hs_sub (measure_ne_top μ _) hmin_s hdV
    have hd_le := volume_inter_ball_deriv_le hmin.measurableSet x₀ hs_pos hdV
    have hmul_le : ballGluingConstant * deriv V s ≤ C * t ^ (d - 1) := by
      calc
        ballGluingConstant * deriv V s ≤
            ballGluingConstant * ((d : ℝ) * volume.real (ball (0 : Space d) 1) * s ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left hd_le ballGluingConstant_pos.le
        _ = C * s ^ (d - 1) := by dsimp [C]; ring
        _ ≤ C * t ^ (d - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs_pos.le hs_mem.2.le _) hC_nonneg
    calc
      variationalPerimeter b F (ball x₀ r) = μ (ball x₀ r) :=
        (hμ_open (ball x₀ r) isOpen_ball (ball_subset_ball (by linarith))).symm
      _ ≤ μ (closedBall x₀ s) :=
        measure_mono ((ball_subset_ball hs_mem.1.le).trans ball_subset_closedBall)
      _ ≤ ENNReal.ofReal (ballGluingConstant * deriv V s) := hclosed_le
      _ ≤ ENNReal.ofReal (C * t ^ (d - 1)) := ENNReal.ofReal_le_ofReal hmul_le
  have hlim : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (C * t ^ (d - 1))) (𝓝[>] r)
      (𝓝 (ENNReal.ofReal (C * r ^ (d - 1)))) := by
    have hc : Continuous (fun t : ℝ ↦ ENNReal.ofReal (C * t ^ (d - 1))) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow (d - 1)))
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : r < r + δ)] with t ht
  exact hstep t ht

/-- Real-valued form of `IsLocalPerimeterMinimizer.perimeter_ball_le`. -/
theorem IsLocalPerimeterMinimizer.perimeter_ball_toReal_le {d : ℕ} (hd : 1 ≤ d)
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {F Ω : Set (Space d)}
    (hmin : IsLocalPerimeterMinimizer b F Ω) {x₀ : Space d} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω) :
    (variationalPerimeter b F (ball x₀ r)).toReal ≤
      ballGluingConstant * (d : ℝ) * volume.real (ball (0 : Space d) 1) * r ^ (d - 1) := by
  refine ENNReal.toReal_le_of_le_ofReal ?_ (hmin.perimeter_ball_le hd hr hsub)
  exact mul_nonneg
    (mul_nonneg (mul_nonneg ballGluingConstant_pos.le (Nat.cast_nonneg d)) measureReal_nonneg)
    (pow_nonneg hr.le _)

/-! ### 2. Local compact-perturbation localization and open exhaustion -/

/-- Binary open subadditivity of variational perimeter. -/
theorem variationalPerimeter_union_le_add {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E U B : Set (Space d)}
    (hE : MeasurableSet E) (hU : IsOpen U) (hB : IsOpen B) :
    variationalPerimeter b E (U ∪ B) ≤
      variationalPerimeter b E U + variationalPerimeter b E B := by
  unfold variationalPerimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦
    iSup_le fun hs ↦ iSup_le fun hunit ↦ ?_
  let L : Set (Space d) := tsupport F \ B
  have hL_comp : IsCompact L := hc.diff hB
  have hLU : L ⊆ U := fun x hx ↦ (hs hx.1).resolve_right hx.2
  obtain ⟨W, hWo, hLW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hL_comp hU hLU
  obtain ⟨V, hVo, hWV, hVU, _⟩ := exists_open_between_and_isCompact_closure hWc hU hWU
  obtain ⟨χ, hχsmooth, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) hVo isClosed_closure hWV
  have hχval (x : Space d) : χ x ∈ Icc (0 : ℝ) 1 := hχrange ⟨x, rfl⟩
  have hχU : tsupport χ ⊆ U := by
    change closure (Function.support χ) ⊆ U
    rwa [hχsupport]
  let F₁ : Space d → Space d := fun x ↦ χ x • F x
  let F₂ : Space d → Space d := fun x ↦ (1 - χ x) • F x
  have hF₁ : ContDiff ℝ 1 F₁ := hχsmooth.smul hF
  have hF₂ : ContDiff ℝ 1 F₂ := (contDiff_const.sub hχsmooth).smul hF
  have hs₁K : tsupport F₁ ⊆ tsupport F := tsupport_smul_subset_right χ F
  have hs₂K : tsupport F₂ ⊆ tsupport F := tsupport_smul_subset_right (fun x ↦ 1 - χ x) F
  have hc₁ : HasCompactSupport F₁ := hc.of_isClosed_subset (isClosed_tsupport _) hs₁K
  have hc₂ : HasCompactSupport F₂ := hc.of_isClosed_subset (isClosed_tsupport _) hs₂K
  have hs₁U : tsupport F₁ ⊆ U := (tsupport_smul_subset_left χ F).trans hχU
  have hs₂B : tsupport F₂ ⊆ B := by
    intro x hx
    by_contra hxB
    have hxL : x ∈ L := ⟨hs₂K hx, hxB⟩
    have hxnot : x ∉ tsupport F₂ := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [hWo.mem_nhds (hLW hxL)] with y hy
      have h1 : χ y = 1 := (hχone y).mp (subset_closure hy)
      simp [F₂, h1]
    exact hxnot hx
  have hu₁ (x : Space d) : ‖F₁ x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (hχval x).1]
    exact (mul_le_mul_of_nonneg_left (hunit x) (hχval x).1).trans
      (by simpa only [mul_one] using (hχval x).2)
  have hu₂ (x : Space d) : ‖F₂ x‖ ≤ 1 := by
    have h1χ : 0 ≤ 1 - χ x := sub_nonneg.mpr (hχval x).2
    have h1χ_le : 1 - χ x ≤ 1 := sub_le_self 1 (hχval x).1
    rw [norm_smul, Real.norm_of_nonneg h1χ]
    exact (mul_le_mul_of_nonneg_left (hunit x) h1χ).trans (by simpa only [mul_one] using h1χ_le)
  have hFsum : F = fun x ↦ F₁ x + F₂ x := by
    funext x
    simp only [F₁, F₂, ← add_smul, add_sub_cancel, one_smul]
  have hdiv (x : Space d) :
      fieldDivergence b F x = fieldDivergence b F₁ x + fieldDivergence b F₂ x := by
    have hd : fderiv ℝ F x = fderiv ℝ F₁ x + fderiv ℝ F₂ x := by
      rw [hFsum]
      exact fderiv_add (hF₁.differentiable_one x) (hF₂.differentiable_one x)
    simp only [fieldDivergence, hd, add_apply, inner_add_right, Finset.sum_add_distrib]
  have hint_eq (G : Space d → Space d) (hGs : tsupport G ⊆ tsupport F) :
      (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x) =
        ∫ x in tsupport F, E.indicator (fieldDivergence b G) x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [fieldDivergence_zero_of_notMem_tsupport b G (fun hh ↦ hx (hGs hh)), mul_zero]]
    refine setIntegral_congr_fun hc.measurableSet fun x _ ↦ ?_
    by_cases hxE : x ∈ E <;> simp [hxE]
  have hi₁ : IntegrableOn (E.indicator (fieldDivergence b F₁)) (tsupport F) :=
    ((fieldDivergence_continuous b hF₁).continuousOn.integrableOn_compact hc).indicator hE
  have hi₂ : IntegrableOn (E.indicator (fieldDivergence b F₂)) (tsupport F) :=
    ((fieldDivergence_continuous b hF₂).continuousOn.integrableOn_compact hc).indicator hE
  have hsplit : (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
      (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x) +
      (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x) := by
    rw [hint_eq F Subset.rfl, hint_eq F₁ hs₁K, hint_eq F₂ hs₂K, ← integral_add hi₁ hi₂]
    refine setIntegral_congr_fun hc.measurableSet fun x _ ↦ ?_
    by_cases hxE : x ∈ E <;> simp [hxE, hdiv x]
  rw [hsplit]
  calc
    ENNReal.ofReal ‖(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x) +
        ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x‖ ≤
      ENNReal.ofReal (‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x‖ +
        ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x‖) :=
      ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x‖ +
        ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x‖ :=
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ (⨆ (G : Space d → Space d) (_ : ContDiff ℝ 1 G) (_ : HasCompactSupport G)
          (_ : tsupport G ⊆ U) (_ : ∀ x, ‖G x‖ ≤ 1),
          ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x‖) +
        (⨆ (G : Space d → Space d) (_ : ContDiff ℝ 1 G) (_ : HasCompactSupport G)
          (_ : tsupport G ⊆ B) (_ : ∀ x, ‖G x‖ ≤ 1),
          ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x‖) :=
      add_le_add
        (le_iSup_of_le F₁ (le_iSup_of_le hF₁ (le_iSup_of_le hc₁
          (le_iSup_of_le hs₁U (le_iSup_of_le hu₁ le_rfl)))))
        (le_iSup_of_le F₂ (le_iSup_of_le hF₂ (le_iSup_of_le hc₂
          (le_iSup_of_le hs₂B (le_iSup_of_le hu₂ le_rfl)))))

/-- If `D` agrees a.e. with `E` outside a compact subset `K ⊆ V_pert` of an open set `V_pert`,
then `P(D, U) ≤ P(D, V_pert) + P(E, U)` on every test region `U`. -/
theorem variationalPerimeter_le_add_of_compact_perturbation {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E D K V_pert U : Set (Space d)}
    (hD : MeasurableSet D) (hK : IsCompact K) (hV_pert : IsOpen V_pert) (hKV : K ⊆ V_pert)
    (hED : ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) :
    variationalPerimeter b D U ≤
      variationalPerimeter b D V_pert + variationalPerimeter b E U := by
  obtain ⟨W, hWo, hKW, hWV_pert, hWc⟩ := exists_open_between_and_isCompact_closure hK hV_pert hKV
  obtain ⟨V, hVo, hWV, hVV_pert, _⟩ := exists_open_between_and_isCompact_closure hWc hV_pert hWV_pert
  obtain ⟨χ, hχsmooth, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) hVo isClosed_closure hWV
  have hχval (x : Space d) : χ x ∈ Icc (0 : ℝ) 1 := hχrange ⟨x, rfl⟩
  have hχV : tsupport χ ⊆ V_pert := by
    change closure (Function.support χ) ⊆ V_pert
    rwa [hχsupport]
  unfold variationalPerimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦
    iSup_le fun hs ↦ iSup_le fun hunit ↦ ?_
  let F₁ : Space d → Space d := fun x ↦ χ x • F x
  let F₂ : Space d → Space d := fun x ↦ (1 - χ x) • F x
  have hF₁ : ContDiff ℝ 1 F₁ := hχsmooth.smul hF
  have hF₂ : ContDiff ℝ 1 F₂ := (contDiff_const.sub hχsmooth).smul hF
  have hs₁K : tsupport F₁ ⊆ tsupport F := tsupport_smul_subset_right χ F
  have hs₂K : tsupport F₂ ⊆ tsupport F := tsupport_smul_subset_right (fun x ↦ 1 - χ x) F
  have hc₁ : HasCompactSupport F₁ := hc.of_isClosed_subset (isClosed_tsupport _) hs₁K
  have hc₂ : HasCompactSupport F₂ := hc.of_isClosed_subset (isClosed_tsupport _) hs₂K
  have hs₁V : tsupport F₁ ⊆ V_pert := (tsupport_smul_subset_left χ F).trans hχV
  have hs₂U : tsupport F₂ ⊆ U := hs₂K.trans hs
  have hu₁ (x : Space d) : ‖F₁ x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (hχval x).1]
    exact (mul_le_mul_of_nonneg_left (hunit x) (hχval x).1).trans
      (by simpa only [mul_one] using (hχval x).2)
  have hu₂ (x : Space d) : ‖F₂ x‖ ≤ 1 := by
    have h1χ : 0 ≤ 1 - χ x := sub_nonneg.mpr (hχval x).2
    have h1χ_le : 1 - χ x ≤ 1 := sub_le_self 1 (hχval x).1
    rw [norm_smul, Real.norm_of_nonneg h1χ]
    exact (mul_le_mul_of_nonneg_left (hunit x) h1χ).trans (by simpa only [mul_one] using h1χ_le)
  have hFsum : F = fun x ↦ F₁ x + F₂ x := by
    funext x
    simp only [F₁, F₂, ← add_smul, add_sub_cancel, one_smul]
  have hdiv (x : Space d) :
      fieldDivergence b F x = fieldDivergence b F₁ x + fieldDivergence b F₂ x := by
    have hd : fderiv ℝ F x = fderiv ℝ F₁ x + fderiv ℝ F₂ x := by
      rw [hFsum]
      exact fderiv_add (hF₁.differentiable_one x) (hF₂.differentiable_one x)
    simp only [fieldDivergence, hd, add_apply, inner_add_right, Finset.sum_add_distrib]
  have hint_eq (G : Space d → Space d) (hGs : tsupport G ⊆ tsupport F) :
      (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x) =
        ∫ x in tsupport F, D.indicator (fieldDivergence b G) x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [fieldDivergence_zero_of_notMem_tsupport b G (fun hh ↦ hx (hGs hh)), mul_zero]]
    refine setIntegral_congr_fun hc.measurableSet fun x _ ↦ ?_
    by_cases hxD : x ∈ D <;> simp [hxD]
  have hi₁ : IntegrableOn (D.indicator (fieldDivergence b F₁)) (tsupport F) :=
    ((fieldDivergence_continuous b hF₁).continuousOn.integrableOn_compact hc).indicator hD
  have hi₂ : IntegrableOn (D.indicator (fieldDivergence b F₂)) (tsupport F) :=
    ((fieldDivergence_continuous b hF₂).continuousOn.integrableOn_compact hc).indicator hD
  have hsplit : (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
      (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x) +
      (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x) := by
    rw [hint_eq F Subset.rfl, hint_eq F₁ hs₁K, hint_eq F₂ hs₂K, ← integral_add hi₁ hi₂]
    refine setIntegral_congr_fun hc.measurableSet fun x _ ↦ ?_
    by_cases hxD : x ∈ D <;> simp [hxD, hdiv x]
  have hF₂_DE : (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x) =
      ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x := by
    apply integral_congr_ae
    filter_upwards [hED] with x hx
    by_cases hxK : x ∈ K
    · have hxnot : x ∉ tsupport F₂ := by
        rw [notMem_tsupport_iff_eventuallyEq]
        filter_upwards [hWo.mem_nhds (hKW hxK)] with y hy
        have h1 : χ y = 1 := (hχone y).mp (subset_closure hy)
        simp [F₂, h1]
      simp [fieldDivergence_zero_of_notMem_tsupport b F₂ hxnot]
    · have heq := hx hxK
      by_cases hxE : x ∈ E
      · simp [hxE, heq.mp hxE]
      · have hxD : x ∉ D := fun hh ↦ hxE (heq.mpr hh)
        simp [hxE, hxD]
  rw [hsplit, hF₂_DE]
  calc
    ENNReal.ofReal ‖(∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x) +
        ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x‖ ≤
      ENNReal.ofReal (‖∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x‖ +
        ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x‖) :=
      ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x‖ +
        ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x‖ :=
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ (⨆ (G : Space d → Space d) (_ : ContDiff ℝ 1 G) (_ : HasCompactSupport G)
          (_ : tsupport G ⊆ V_pert) (_ : ∀ x, ‖G x‖ ≤ 1),
          ENNReal.ofReal ‖∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x‖) +
        (⨆ (G : Space d → Space d) (_ : ContDiff ℝ 1 G) (_ : HasCompactSupport G)
          (_ : tsupport G ⊆ U) (_ : ∀ x, ‖G x‖ ≤ 1),
          ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x‖) :=
      add_le_add
        (le_iSup_of_le F₁ (le_iSup_of_le hF₁ (le_iSup_of_le hc₁
          (le_iSup_of_le hs₁V (le_iSup_of_le hu₁ le_rfl)))))
        (le_iSup_of_le F₂ (le_iSup_of_le hF₂ (le_iSup_of_le hc₂
          (le_iSup_of_le hs₂U (le_iSup_of_le hu₂ le_rfl)))))

/-- Local form of `perimeter_measure_eq_of_subset_ae_region` when `μ` and `ν` represent
variational perimeter only on open subsets of an ambient open set `W`. -/
theorem perimeter_measure_eq_of_subset_ae_region_on {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E D W O A : Set (Space d)}
    (μ ν : Measure (Space d)) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (hμ : ∀ U, IsOpen U → U ⊆ W → μ U = variationalPerimeter b E U)
    (hν : ∀ U, IsOpen U → U ⊆ W → ν U = variationalPerimeter b D U)
    (hO : IsOpen O) (hOW : O ⊆ W) (hED : ∀ᵐ x ∂volume, x ∈ O → (x ∈ E ↔ x ∈ D))
    (hA : MeasurableSet A) (hAO : A ⊆ O) : μ A = ν A := by
  have hres : μ.restrict O = ν.restrict O := by
    apply Measure.OuterRegular.ext_isOpen
    intro U hU
    rw [Measure.restrict_apply hU.measurableSet, Measure.restrict_apply hU.measurableSet,
      hμ _ (hU.inter hO) (inter_subset_right.trans hOW),
      hν _ (hU.inter hO) (inter_subset_right.trans hOW)]
    apply variationalPerimeter_congr_ae_on b
    filter_upwards [hED] with x hx hxU
    exact hx hxU.2
  have he := congrArg (fun ρ : Measure (Space d) ↦ ρ A) hres
  simpa only [Measure.restrict_apply hA, inter_eq_left.mpr hAO] using he

/-- Local compact-perturbation localization: if `E` and `D` agree a.e. outside a compact set
`K ⊆ B ∩ U` (`B, U` open) and `P(E, B) ≠ ⊤`, then `P(E, B) ≤ P(D, B)` transfers to
`P(E, U) ≤ P(D, U)` without assuming global finiteness of `E` or `D`. -/
theorem perimeter_comparison_localize_of_compact_perturbation {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E D K B U : Set (Space d)}
    (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hK : IsCompact K) (hB : IsOpen B) (hU : IsOpen U)
    (hKB : K ⊆ B) (hKU : K ⊆ U)
    (hEB : variationalPerimeter b E B ≠ ⊤)
    (hED : ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D))
    (hcomp : variationalPerimeter b E B ≤ variationalPerimeter b D B) :
    variationalPerimeter b E U ≤ variationalPerimeter b D U := by
  by_cases hDU : variationalPerimeter b D U = ⊤
  · rw [hDU]
    exact le_top
  have hDE : ∀ᵐ x ∂volume, x ∉ K → (x ∈ D ↔ x ∈ E) := by
    filter_upwards [hED] with x hx hxK
    exact (hx hxK).symm
  have hEU : variationalPerimeter b E U ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hEB, hDU⟩)
      (variationalPerimeter_le_add_of_compact_perturbation b hE hK hB hKB hDE)
  have hDB : variationalPerimeter b D B ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hDU, hEB⟩)
      (variationalPerimeter_le_add_of_compact_perturbation b hD hK hU hKU hED)
  let W : Set (Space d) := U ∪ B
  have hW : IsOpen W := hU.union hB
  have hEW : variationalPerimeter b E W ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hEU, hEB⟩)
      (variationalPerimeter_union_le_add b hE hU hB)
  have hDW : variationalPerimeter b D W ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hDU, hDB⟩)
      (variationalPerimeter_union_le_add b hD hU hB)
  obtain ⟨σE, hmassE, -, -, hdistE⟩ :=
    exists_perimeter_vector_measure_concentrated b hE hW.measurableSet hEW
  obtain ⟨σD, hmassD, -, -, hdistD⟩ :=
    exists_perimeter_vector_measure_concentrated b hD hW.measurableSet hDW
  let μ := σE.variation
  let ν := σD.variation
  let _ : IsFiniteMeasure μ := ⟨by rw [hmassE]; exact lt_top_iff_ne_top.mpr hEW⟩
  let _ : IsFiniteMeasure ν := ⟨by rw [hmassD]; exact lt_top_iff_ne_top.mpr hDW⟩
  have hμ (V : Set (Space d)) (hV : IsOpen V) (hVW : V ⊆ W) :
      μ V = variationalPerimeter b E V :=
    variation_eq_variationalPerimeter_of_representation b σE hdistE hV hVW
  have hν (V : Set (Space d)) (hV : IsOpen V) (hVW : V ⊆ W) :
      ν V = variationalPerimeter b D V :=
    variation_eq_variationalPerimeter_of_representation b σD hdistD hV hVW
  let O : Set (Space d) := W \ K
  have hO : IsOpen O := hW.sdiff hK.isClosed
  have hEDO : ∀ᵐ x ∂volume, x ∈ O → (x ∈ E ↔ x ∈ D) := by
    filter_upwards [hED] with x hx hxO
    exact hx hxO.2
  have houter : μ (B \ U) = ν (B \ U) :=
    perimeter_measure_eq_of_subset_ae_region_on b μ ν hμ hν hO sdiff_subset hEDO
      (hB.measurableSet.diff hU.measurableSet)
      (fun x hx ↦ ⟨Or.inr hx.1, fun hxK ↦ hx.2 (hKU hxK)⟩)
  have hrest : μ (U \ B) = ν (U \ B) :=
    perimeter_measure_eq_of_subset_ae_region_on b μ ν hμ hν hO sdiff_subset hEDO
      (hU.measurableSet.diff hB.measurableSet)
      (fun x hx ↦ ⟨Or.inl hx.1, fun hxK ↦ hx.2 (hKB hxK)⟩)
  have hcomp_meas : μ B ≤ ν B := by
    rw [hμ B hB subset_union_right, hν B hB subset_union_right]
    exact hcomp
  have hinter : μ (B ∩ U) ≤ ν (B ∩ U) := by
    rw [← measure_inter_add_sdiff B hU.measurableSet (μ := μ),
      ← measure_inter_add_sdiff B hU.measurableSet (μ := ν), houter] at hcomp_meas
    exact (ENNReal.add_le_add_iff_right (measure_ne_top ν _)).mp hcomp_meas
  rw [← hμ U hU subset_union_left, ← hν U hU subset_union_left,
    ← measure_inter_add_sdiff U hB.measurableSet (μ := μ),
    ← measure_inter_add_sdiff U hB.measurableSet (μ := ν), hrest, inter_comm U B]
  exact add_le_add hinter le_rfl

/-- Every compact subset of `ball c₀ R₀` (`0 < R₀`) lies in a strictly smaller concentric ball. -/
theorem exists_radii_lt_subset_ball_of_isCompact {d : ℕ} {c₀ : Space d} {R₀ : ℝ} (hR₀ : 0 < R₀)
    {K : Set (Space d)} (hK : IsCompact K) (hKsub : K ⊆ ball c₀ R₀) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ r₂ < R₀ ∧ K ⊆ ball c₀ r₁ := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨R₀ / 3, 2 * R₀ / 3, by positivity, by linarith, by linarith, empty_subset _⟩
  · obtain ⟨y₀, hy₀, hmax⟩ :=
      hK.exists_isMaxOn hKne (continuous_id.dist continuous_const).continuousOn
    have hd₀_lt : dist y₀ c₀ < R₀ := mem_ball.mp (hKsub hy₀)
    have hd₀_nonneg : 0 ≤ dist y₀ c₀ := dist_nonneg
    let r₁ : ℝ := dist y₀ c₀ + (R₀ - dist y₀ c₀) / 3
    let r₂ : ℝ := dist y₀ c₀ + 2 * (R₀ - dist y₀ c₀) / 3
    refine ⟨r₁, r₂, by dsimp [r₁]; linarith, by dsimp [r₁, r₂]; linarith,
      by dsimp [r₂]; linarith, fun y hy ↦ ?_⟩
    have hle : dist y c₀ ≤ dist y₀ c₀ := hmax hy
    exact mem_ball.mpr (by dsimp [r₁]; linarith)

/-- Local perimeter minimality on every origin-centered ball upgrades to `univ`. -/
theorem isLocalPerimeterMinimizer_univ_of_ball {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E : Set (Space d)}
    (h : ∀ R : ℝ, 0 < R → IsLocalPerimeterMinimizer b E (ball 0 R)) :
    IsLocalPerimeterMinimizer b E univ := by
  have hE : MeasurableSet E := (h 1 zero_lt_one).measurableSet
  refine isLocalPerimeterMinimizer_univ b hE
    (fun n ↦ (h ((n : ℝ) + 2) (by positivity)).perimeter_ball_ne_top 0 ((n : ℝ) + 1)
      (by positivity) (closedBall_subset_ball (by linarith))) ?_
  intro U D K hU hD hK hKU hED
  obtain ⟨n, hn⟩ := compact_subset_perimeter_ball hK
  let B : Set (Space d) := ball 0 ((n : ℝ) + 1)
  have hR₂ : IsLocalPerimeterMinimizer b E (ball 0 ((n : ℝ) + 2)) :=
    h ((n : ℝ) + 2) (by positivity)
  have hEB : variationalPerimeter b E B ≠ ⊤ :=
    hR₂.perimeter_ball_ne_top 0 ((n : ℝ) + 1) (by positivity)
      (closedBall_subset_ball (by linarith))
  have hcomp : variationalPerimeter b E B ≤ variationalPerimeter b D B :=
    hR₂.minimizes B D K isOpen_ball (ball_subset_ball (by linarith)) hD hK hn hED
  exact perimeter_comparison_localize_of_compact_perturbation b hE hD hK isOpen_ball hU
    hn hKU hEB hED hcomp

/-- Local perimeter minimality on all strictly smaller concentric balls upgrades to `ball c₀ R₀`. -/
theorem isLocalPerimeterMinimizer_ball_of_lt {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E : Set (Space d)}
    {c₀ : Space d} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (h : ∀ r : ℝ, 0 < r → r < R₀ → IsLocalPerimeterMinimizer b E (ball c₀ r)) :
    IsLocalPerimeterMinimizer b E (ball c₀ R₀) where
  measurableSet := (h (R₀ / 2) (half_pos hR₀) (half_lt_self hR₀)).measurableSet
  isOpen_domain := isOpen_ball
  perimeter_ball_ne_top x₀ ρ hρ hcb := by
    obtain ⟨r₁, r₂, hr₁, hr₁₂, hr₂R₀, hsub₁⟩ :=
      exists_radii_lt_subset_ball_of_isCompact hR₀ (isCompact_closedBall x₀ ρ) hcb
    exact (h r₁ hr₁ (hr₁₂.trans hr₂R₀)).perimeter_ball_ne_top x₀ ρ hρ hsub₁
  minimizes U D K hU hUsub hD hK hKU hED := by
    have hE : MeasurableSet E := (h (R₀ / 2) (half_pos hR₀) (half_lt_self hR₀)).measurableSet
    obtain ⟨r₁, r₂, hr₁, hr₁₂, hr₂R₀, hKB⟩ :=
      exists_radii_lt_subset_ball_of_isCompact hR₀ hK (hKU.trans hUsub)
    let B : Set (Space d) := ball c₀ r₁
    have hEB : variationalPerimeter b E B ≠ ⊤ :=
      (h r₂ (hr₁.trans hr₁₂) hr₂R₀).perimeter_ball_ne_top c₀ r₁ hr₁
        (closedBall_subset_ball hr₁₂)
    have hcomp : variationalPerimeter b E B ≤ variationalPerimeter b D B :=
      (h r₂ (hr₁.trans hr₁₂) hr₂R₀).minimizes B D K isOpen_ball
        (ball_subset_ball hr₁₂.le) hD hK hKB hED
    exact perimeter_comparison_localize_of_compact_perturbation b hE hD hK isOpen_ball hU
      hKB hKU hEB hED hcomp

/-! ### 3. Summable-subsequence spherical slicing and concentric-ball comparison -/

/-- Set integral of the indicator difference equals the real volume of the symmetric difference. -/
theorem setIntegral_norm_indicator_sub_eq_volume_symmDiff {d : ℕ}
    {A B S : Set (Space d)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ x in S, ‖A.indicator (fun _ ↦ (1 : ℝ)) x - B.indicator (fun _ ↦ (1 : ℝ)) x‖) =
      volume.real (symmDiff A B ∩ S) := by
  have hpoint : (fun x ↦ ‖A.indicator (fun _ ↦ (1 : ℝ)) x - B.indicator (fun _ ↦ (1 : ℝ)) x‖) =
      (symmDiff A B).indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [symmDiff, hxA, hxB]
  rw [hpoint, setIntegral_indicator (hA.symmDiff hB), setIntegral_const, smul_eq_mul,
    mul_one, inter_comm]

/-- A sequence of real numbers tending to `0` (and eventually nonnegative) admits a strictly
increasing subsequence bounded by `(1 / 2) ^ k` starting at or after any prescribed index `J₀`. -/
theorem exists_strictMono_le_geometric_two {u : ℕ → ℝ} (ht : Tendsto u atTop (𝓝 0)) (J₀ : ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, J₀ ≤ φ k) ∧ ∀ k, u (φ k) ≤ (1 / 2 : ℝ) ^ k := by
  have hex (k : ℕ) : ∃ N : ℕ, J₀ ≤ N ∧ ∀ j ≥ N, u j ≤ (1 / 2 : ℝ) ^ k := by
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hpos))
    exact ⟨max J₀ N₁, le_max_left _ _, fun j hj ↦ (hN₁ j ((le_max_right J₀ N₁).trans hj)).le⟩
  choose N hNJ₀ hN using hex
  let φ : ℕ → ℕ := fun k ↦ Nat.recOn k (N 0) (fun m prev ↦ max (prev + 1) (N (m + 1)))
  have hφ_mono : StrictMono φ :=
    strictMono_nat_of_lt_succ fun k ↦ lt_of_lt_of_le (Nat.lt_succ_self (φ k)) (le_max_left _ _)
  have hφ_ge_N (k : ℕ) : N k ≤ φ k := by
    cases k with
    | zero => exact le_rfl
    | succ m => exact le_max_right _ _
  exact ⟨φ, hφ_mono, fun k ↦ (hNJ₀ k).trans (hφ_ge_N k), fun k ↦ hN k (φ k) (hφ_ge_N k)⟩

/-- Every monotone function `V : ℝ → ℝ` has `0 ≤ deriv V r` at every point `r : ℝ`. -/
theorem monotone_deriv_nonneg_everywhere {V : ℝ → ℝ} (hV : Monotone V) (r : ℝ) :
    0 ≤ deriv V r := by
  by_cases hd : DifferentiableAt ℝ V r
  · exact monotone_hasDerivAt_nonneg hV hd.hasDerivAt
  · rw [deriv_zero_of_not_differentiableAt hd]

/-- Fast-subsequence radial derivative decay: if `E_seq j → E` in `L¹(closedBall x₀ R)` (`0 < R`),
then along a strictly increasing subsequence `φ` with `J₀ ≤ φ k`, for Lebesgue-a.e. `s ∈ Ioo 0 R`
the symmetric-difference radial volume derivatives `deriv (ρ ↦ |symmDiff E (E_seq (φ k)) ∩ B_ρ|) s`
converge to `0` as `k → ∞`. -/
theorem exists_subsequence_ae_deriv_symmDiff_ball_tendsto_zero {d : ℕ}
    {E_seq : ℕ → Set (Space d)} {E : Set (Space d)} (hE : MeasurableSet E)
    {J₀ : ℕ} (hE_seq : ∀ j ≥ J₀, MeasurableSet (E_seq j))
    (x₀ : Space d) {R : ℝ} (hR : 0 < R)
    (ht : Tendsto (fun j ↦ ∫ x in closedBall x₀ R,
      ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
      atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, J₀ ≤ φ k) ∧
      ∀ᵐ s : ℝ ∂volume, s ∈ Ioo 0 R →
        Tendsto (fun k ↦ deriv (fun ρ ↦ volume.real (symmDiff E (E_seq (φ k)) ∩ ball x₀ ρ)) s)
          atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hφJ₀, hφ_le⟩ := exists_strictMono_le_geometric_two ht J₀
  let W : ℕ → ℝ → ℝ := fun k ρ ↦ volume.real (symmDiff E (E_seq (φ k)) ∩ ball x₀ ρ)
  have hW_mono (k : ℕ) : Monotone (W k) :=
    monotone_volume_real_inter_ball (symmDiff E (E_seq (φ k))) x₀
  have hW_zero (k : ℕ) : W k 0 = 0 := by
    simp [W]
  have hW_R_le (k : ℕ) : W k R ≤ (1 / 2 : ℝ) ^ k := by
    have hmeas_k : MeasurableSet (E_seq (φ k)) := hE_seq (φ k) (hφJ₀ k)
    have hmono_R : W k R ≤ volume.real (symmDiff E (E_seq (φ k)) ∩ closedBall x₀ R) :=
      measureReal_mono (inter_subset_inter_right _ ball_subset_closedBall)
        ((measure_mono inter_subset_right).trans_lt (isCompact_closedBall x₀ R).measure_lt_top).ne
    have hsymm_eq : volume.real (symmDiff E (E_seq (φ k)) ∩ closedBall x₀ R) =
        ∫ x in closedBall x₀ R,
          ‖(E_seq (φ k)).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖ := by
      rw [setIntegral_norm_indicator_sub_eq_volume_symmDiff hmeas_k hE, symmDiff_comm]
    exact hmono_R.trans (hsymm_eq.trans_le (hφ_le k))
  have hderiv_nonneg (k : ℕ) (s : ℝ) : 0 ≤ deriv (W k) s :=
    monotone_deriv_nonneg_everywhere (hW_mono k) s
  have hderiv_int (k : ℕ) : IntegrableOn (deriv (W k)) (Ioo 0 R) volume :=
    (monotone_setIntegral_deriv_Ioo_le (hW_mono k) hR.le).1
  have hderiv_le (k : ℕ) : (∫ s in Ioo 0 R, deriv (W k) s) ≤ (1 / 2 : ℝ) ^ k := by
    have h1 := (monotone_setIntegral_deriv_Ioo_le (hW_mono k) hR.le).2
    rw [hW_zero k, sub_zero] at h1
    exact h1.trans (hW_R_le k)
  let μ_res := volume.restrict (Ioo 0 R)
  have haemeas (k : ℕ) : AEMeasurable (fun s ↦ ENNReal.ofReal (deriv (W k) s)) μ_res :=
    (hderiv_int k).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hlint_le (k : ℕ) :
      (∫⁻ s, ENNReal.ofReal (deriv (W k) s) ∂μ_res) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hderiv_int k)
      (Eventually.of_forall fun s ↦ hderiv_nonneg k s)]
    exact ENNReal.ofReal_le_ofReal (hderiv_le k)
  have htsum_lt_top : (∫⁻ s, (∑' k, ENNReal.ofReal (deriv (W k) s)) ∂μ_res) < ⊤ := by
    rw [lintegral_tsum haemeas]
    calc
      (∑' k, ∫⁻ s, ENNReal.ofReal (deriv (W k) s) ∂μ_res) ≤
          ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := ENNReal.tsum_le_tsum hlint_le
      _ = ENNReal.ofReal (∑' k : ℕ, (1 / 2 : ℝ) ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) summable_geometric_two).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hae_fin : ∀ᵐ s ∂μ_res, (∑' k, ENNReal.ofReal (deriv (W k) s)) < ⊤ :=
    ae_lt_top' (AEMeasurable.tsum haemeas) htsum_lt_top.ne
  rw [ae_restrict_iff' measurableSet_Ioo] at hae_fin
  refine ⟨φ, hφ, hφJ₀, ?_⟩
  filter_upwards [hae_fin] with s hs hs_mem
  have hne_top : (∑' k, ENNReal.ofReal (deriv (W k) s)) ≠ ⊤ := (hs hs_mem).ne
  have hlim_enn : Tendsto (fun k ↦ ENNReal.ofReal (deriv (W k) s)) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne_top
  have hlim_real := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim_enn
  rw [ENNReal.toReal_zero] at hlim_real
  refine hlim_real.congr fun k ↦ ?_
  simp [W, ENNReal.toReal_ofReal (hderiv_nonneg k s)]

/-- Core spherical-gluing comparison along a fast subsequence: if `D` agrees a.e. with `E` outside
`closedBall x₀ r₀` (`0 ≤ r₀ < r_hi`, `closedBall x₀ r_hi ⊆ Ω`) and `P(D, ball x₀ r_hi) ≠ ⊤`,
then along a strictly increasing subsequence `φ` there exists an intermediate good radius
`s ∈ Ioo r₀ r_hi` where `P(E_seq (φ k), ball x₀ s) ≤ P(D, ball x₀ s) + o(1)`. -/
theorem exists_subsequence_radius_perimeter_ball_le_add_error {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E D Ω : Set (Space d)}
    (hmin : ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E) (hD : MeasurableSet D)
    {x₀ : Space d} {r₀ r_hi : ℝ} (hr₀ : 0 ≤ r₀) (hr : r₀ < r_hi)
    (hsub : closedBall x₀ r_hi ⊆ Ω)
    (hPD : variationalPerimeter b D (ball x₀ r_hi) ≠ ⊤)
    (hED : ∀ᵐ x ∂volume, x ∉ closedBall x₀ r₀ → (x ∈ E ↔ x ∈ D))
    (ht : Tendsto (fun j ↦ ∫ x in closedBall x₀ r_hi,
      ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
      atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (s : ℝ) (err : ℕ → ℝ≥0∞),
      StrictMono φ ∧ s ∈ Ioo r₀ r_hi ∧ Tendsto err atTop (𝓝 0) ∧
      (∀ k, IsLocalPerimeterMinimizer b (E_seq (φ k)) Ω) ∧
      ∀ k, variationalPerimeter b (E_seq (φ k)) (ball x₀ s) ≤
        variationalPerimeter b D (ball x₀ s) + err k := by
  have hr_hi_pos : 0 < r_hi := hr₀.trans_lt hr
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp hmin
  obtain ⟨φ, hφ, hφJ₀, hae_decay⟩ :=
    exists_subsequence_ae_deriv_symmDiff_ball_tendsto_zero hE
      (fun j hj ↦ (hJ₀ j hj).measurableSet) x₀ hr_hi_pos ht
  have hmin_φ (k : ℕ) : IsLocalPerimeterMinimizer b (E_seq (φ k)) Ω := hJ₀ (φ k) (hφJ₀ k)
  let Ω₀ : Set (Space d) := ball x₀ r_hi
  obtain ⟨σD, hmassD, -, -, hdistD⟩ :=
    exists_perimeter_vector_measure_concentrated b hD isOpen_ball.measurableSet hPD
  let μD := σD.variation
  let _ : IsFiniteMeasure μD := ⟨by rw [hmassD]; exact lt_top_iff_ne_top.mpr hPD⟩
  have hμD (U : Set (Space d)) (hU : IsOpen U) (hUΩ₀ : U ⊆ Ω₀) :
      μD U = variationalPerimeter b D U :=
    variation_eq_variationalPerimeter_of_representation b σD hdistD hU hUΩ₀
  have hex_μk (k : ℕ) : ∃ μk : Measure (Space d), IsFiniteMeasure μk ∧
      ∀ U, IsOpen U → U ⊆ Ω₀ → μk U = variationalPerimeter b (E_seq (φ k)) U := by
    have hPk := (hmin_φ k).perimeter_ball_ne_top x₀ r_hi hr_hi_pos hsub
    obtain ⟨σk, hmassk, -, -, hdistk⟩ :=
      exists_perimeter_vector_measure_concentrated b (hmin_φ k).measurableSet
        isOpen_ball.measurableSet hPk
    let _ : IsFiniteMeasure σk.variation := ⟨by rw [hmassk]; exact lt_top_iff_ne_top.mpr hPk⟩
    exact ⟨σk.variation, inferInstance,
      fun U hU hUΩ₀ ↦ variation_eq_variationalPerimeter_of_representation b σk hdistk hU hUΩ₀⟩
  choose μk hμk_fin hμk_open using hex_μk
  have hae_glue_all : ∀ᵐ s : ℝ ∂volume, ∀ k : ℕ, s ∈ Ioo 0 r_hi →
      variationalPerimeter b (ballGluedSet x₀ s D (E_seq (φ k))) Ω₀ ≤
        μD (ball x₀ s) + μk k (Ω₀ \ closedBall x₀ s) +
          ENNReal.ofReal (ballGluingConstant *
            deriv (fun ρ ↦ volume.real ((symmDiff D (E_seq (φ k))) ∩ ball x₀ ρ)) s) := by
    rw [ae_all_iff]
    intro k
    let _ : IsFiniteMeasure (μk k) := hμk_fin k
    filter_upwards [ae_radius_ballGluedSet_perimeter_le hd b hD (hmin_φ k).measurableSet
      isOpen_ball μD (μk k) hμD (hμk_open k) x₀ (R := r_hi) Subset.rfl] with s hs hs_mem
    exact (hs hs_mem).2.2.2
  have hae_Ioo : ∀ᵐ s : ℝ ∂volume.restrict (Ioo r₀ r_hi),
      Tendsto (fun k ↦ deriv (fun ρ ↦ volume.real (symmDiff E (E_seq (φ k)) ∩ ball x₀ ρ)) s)
        atTop (𝓝 0) ∧
      ∀ k : ℕ, variationalPerimeter b (ballGluedSet x₀ s D (E_seq (φ k))) Ω₀ ≤
        μD (ball x₀ s) + μk k (Ω₀ \ closedBall x₀ s) +
          ENNReal.ofReal (ballGluingConstant *
            deriv (fun ρ ↦ volume.real ((symmDiff D (E_seq (φ k))) ∩ ball x₀ ρ)) s) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae_decay, hae_glue_all] with s hdec hgl hs_mem
    have hs0 : s ∈ Ioo 0 r_hi := ⟨hr₀.trans_lt hs_mem.1, hs_mem.2⟩
    exact ⟨hdec hs0, fun k ↦ hgl k hs0⟩
  have hne_zero : volume.restrict (Ioo r₀ r_hi) ≠ 0 := by
    intro h0
    have hpos : (volume.restrict (Ioo r₀ r_hi)) univ ≠ 0 := by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hr)).ne'
    exact hpos (by simp [h0])
  obtain ⟨s, ⟨hdec_s, hgl_s⟩, hs_mem⟩ :=
    @Filter.Eventually.exists _ _ _ (ae_neBot.mpr hne_zero)
      (hae_Ioo.and (ae_restrict_mem measurableSet_Ioo))
  have hs_pos : 0 < s := hr₀.trans_lt hs_mem.1
  let a : ℝ := (r₀ + s) / 2
  have har₀ : r₀ < a := by dsimp [a]; linarith [hs_mem.1]
  have has : a < s := by dsimp [a]; linarith [hs_mem.1]
  have hderiv_eq (k : ℕ) :
      deriv (fun ρ ↦ volume.real ((symmDiff D (E_seq (φ k))) ∩ ball x₀ ρ)) s =
        deriv (fun ρ ↦ volume.real (symmDiff E (E_seq (φ k)) ∩ ball x₀ ρ)) s := by
    let VD : ℝ → ℝ := fun ρ ↦ volume.real ((symmDiff D (E_seq (φ k))) ∩ ball x₀ ρ)
    let WE : ℝ → ℝ := fun ρ ↦ volume.real (symmDiff E (E_seq (φ k)) ∩ ball x₀ ρ)
    have hev : VD =ᶠ[𝓝 s] fun ρ ↦ (VD a - WE a) + WE ρ := by
      filter_upwards [isOpen_Ioi.mem_nhds has] with ρ (hρ : a < ρ)
      have hann_eq : volume ((symmDiff D (E_seq (φ k))) ∩ (ball x₀ ρ \ ball x₀ a)) =
          volume (symmDiff E (E_seq (φ k)) ∩ (ball x₀ ρ \ ball x₀ a)) := by
        apply measure_congr
        filter_upwards [hED] with x hx
        simp only [eq_iff_iff, mem_inter_iff, Set.mem_sdiff, mem_ball]
        constructor
        · rintro ⟨hxD, hρx, hax⟩
          have hxnot : x ∉ closedBall x₀ r₀ := by
            rw [mem_closedBall]
            linarith
          have heq := hx hxnot
          refine ⟨?_, hρx, hax⟩
          simpa only [Set.mem_symmDiff, ← heq] using hxD
        · rintro ⟨hxE, hρx, hax⟩
          have hxnot : x ∉ closedBall x₀ r₀ := by
            rw [mem_closedBall]
            linarith
          have heq := hx hxnot
          refine ⟨?_, hρx, hax⟩
          simpa only [Set.mem_symmDiff, heq] using hxE
      have hann_real : volume.real ((symmDiff D (E_seq (φ k))) ∩ (ball x₀ ρ \ ball x₀ a)) =
          volume.real (symmDiff E (E_seq (φ k)) ∩ (ball x₀ ρ \ ball x₀ a)) := by
        simp only [Measure.real, hann_eq]
      have hsdiff_set (S : Set (Space d)) :
          S ∩ (ball x₀ ρ \ ball x₀ a) = (S ∩ ball x₀ ρ) \ (S ∩ ball x₀ a) := by
        ext x
        simp only [mem_inter_iff, Set.mem_sdiff]
        tauto
      have hVD_diff : VD ρ - VD a =
          volume.real ((symmDiff D (E_seq (φ k))) ∩ (ball x₀ ρ \ ball x₀ a)) := by
        dsimp [VD]
        rw [hsdiff_set, measureReal_sdiff
          (inter_subset_inter_right _ (ball_subset_ball hρ.le))
          ((hD.symmDiff (hmin_φ k).measurableSet).inter measurableSet_ball)]
      have hWE_diff : WE ρ - WE a =
          volume.real (symmDiff E (E_seq (φ k)) ∩ (ball x₀ ρ \ ball x₀ a)) := by
        dsimp [WE]
        rw [hsdiff_set, measureReal_sdiff
          (inter_subset_inter_right _ (ball_subset_ball hρ.le))
          ((hE.symmDiff (hmin_φ k).measurableSet).inter measurableSet_ball)]
      linarith
    rw [hev.deriv_eq, deriv_const_add]
  let err : ℕ → ℝ≥0∞ := fun k ↦ ENNReal.ofReal
    (ballGluingConstant * deriv (fun ρ ↦ volume.real (symmDiff E (E_seq (φ k)) ∩ ball x₀ ρ)) s)
  have herr_lim : Tendsto err atTop (𝓝 0) := by
    have hmul := hdec_s.const_mul ballGluingConstant
    rw [mul_zero] at hmul
    simpa [err] using ENNReal.tendsto_ofReal hmul
  refine ⟨φ, s, err, hφ, hs_mem, herr_lim, hmin_φ, fun k ↦ ?_⟩
  let _ : IsFiniteMeasure (μk k) := hμk_fin k
  have hs_sub : closedBall x₀ s ⊆ Ω₀ := closedBall_subset_ball hs_mem.2
  have hmin_gk : variationalPerimeter b (E_seq (φ k)) Ω₀ ≤
      variationalPerimeter b (ballGluedSet x₀ s D (E_seq (φ k))) Ω₀ := by
    refine (hmin_φ k).minimizes Ω₀ (ballGluedSet x₀ s D (E_seq (φ k))) (closedBall x₀ s)
      isOpen_ball (ball_subset_closedBall.trans hsub)
      (measurableSet_ballGluedSet x₀ s hD (hmin_φ k).measurableSet)
      (isCompact_closedBall x₀ s) hs_sub ?_
    refine Eventually.of_forall fun x hx ↦ ?_
    have hxnot : x ∉ ball x₀ s := fun hb ↦ hx (ball_subset_closedBall hb)
    exact (mem_ballGluedSet_of_notMem_ball hxnot).symm
  have htot : μk k Ω₀ ≤ μD (ball x₀ s) + μk k (Ω₀ \ closedBall x₀ s) + err k := by
    rw [hμk_open k Ω₀ isOpen_ball Subset.rfl]
    refine hmin_gk.trans ?_
    simpa only [hderiv_eq k, err] using hgl_s k
  have hsplit : μk k (closedBall x₀ s) + μk k (Ω₀ \ closedBall x₀ s) = μk k Ω₀ := by
    have hinter : Ω₀ ∩ closedBall x₀ s = closedBall x₀ s := inter_eq_right.mpr hs_sub
    have hm := measure_inter_add_sdiff Ω₀ (measurableSet_closedBall (x := x₀) (ε := s)) (μ := μk k)
    rwa [hinter] at hm
  rw [← hsplit, add_comm (μD (ball x₀ s)) (μk k (Ω₀ \ closedBall x₀ s)), add_assoc,
    add_comm (μk k (Ω₀ \ closedBall x₀ s))] at htot
  have hcancel := (ENNReal.add_le_add_iff_right (measure_ne_top (μk k) _)).mp htot
  calc
    variationalPerimeter b (E_seq (φ k)) (ball x₀ s) = μk k (ball x₀ s) :=
      (hμk_open k (ball x₀ s) isOpen_ball (ball_subset_ball hs_mem.2.le)).symm
    _ ≤ μk k (closedBall x₀ s) := measure_mono ball_subset_closedBall
    _ ≤ μD (ball x₀ s) + err k := hcancel
    _ = variationalPerimeter b D (ball x₀ s) + err k := by
      rw [hμD (ball x₀ s) isOpen_ball (ball_subset_ball hs_mem.2.le)]

/-- Lower semicontinuity of variational perimeter when `E_seq j` is only eventually measurable. -/
theorem variationalPerimeter_le_liminf_of_eventually_measurable {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E_seq : ℕ → Set (Space d)}
    {E Ω : Set (Space d)} (hmeas : ∀ᶠ j in atTop, MeasurableSet (E_seq j)) (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0)) :
    variationalPerimeter b E Ω ≤ liminf (fun j ↦ variationalPerimeter b (E_seq j) Ω) atTop := by
  classical
  let E' : ℕ → Set (Space d) := fun j ↦ if MeasurableSet (E_seq j) then E_seq j else ∅
  have hE' (j : ℕ) : MeasurableSet (E' j) := by
    dsimp [E']
    split_ifs with h
    · exact h
    · exact MeasurableSet.empty
  have ht' (K : Set (Space d)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E' j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0) := by
    refine (ht K hK hKΩ).congr' ?_
    filter_upwards [hmeas] with j hj
    simp [E', hj]
  have hlsc := variationalPerimeter_le_liminf b E' E Ω hE' hE ht'
  have hcongr : liminf (fun j ↦ variationalPerimeter b (E' j) Ω) atTop =
      liminf (fun j ↦ variationalPerimeter b (E_seq j) Ω) atTop := by
    refine Filter.liminf_congr ?_
    filter_upwards [hmeas] with j hj
    simp [E', hj]
  rwa [hcongr] at hlsc

/-- Any `L¹_loc(Ω)` limit `E` of sets that are eventually local perimeter minimizers in `Ω`
inherits the dimensional ball-perimeter bound on every `closedBall x₀ r ⊆ Ω`. -/
theorem variationalPerimeter_ball_le_of_eventually_tendsto_indicator {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E Ω : Set (Space d)}
    (hmin : ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {x₀ : Space d} {r : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω) :
    variationalPerimeter b E (ball x₀ r) ≤
      ENNReal.ofReal (ballGluingConstant * (d : ℝ) *
        volume.real (ball (0 : Space d) 1) * r ^ (d - 1)) := by
  let B := ENNReal.ofReal (ballGluingConstant * (d : ℝ) *
    volume.real (ball (0 : Space d) 1) * r ^ (d - 1))
  have hlsc := variationalPerimeter_le_liminf_of_eventually_measurable b
    (hmin.mono fun _ h ↦ h.measurableSet) hE
    (fun K hK hKball ↦ ht K hK (hKball.trans (ball_subset_closedBall.trans hsub)))
  refine hlsc.trans ?_
  have hev : ∀ᶠ j in atTop, variationalPerimeter b (E_seq j) (ball x₀ r) ≤ B :=
    hmin.mono fun _ hj ↦ hj.perimeter_ball_le hd hr hsub
  exact (liminf_le_liminf hev).trans_eq (Filter.liminf_const (f := atTop) B)

/-- Concentric-ball comparison for an `L¹_loc(Ω)` limit `E` of eventually local perimeter
minimizers: if `D` agrees a.e. with `E` outside `closedBall x₀ r₀` (`0 ≤ r₀ < r_hi`,
`closedBall x₀ r_hi ⊆ Ω`), then `P(E, ball x₀ r_hi) ≤ P(D, ball x₀ r_hi)`. -/
theorem variationalPerimeter_ball_le_of_eventually_tendsto_indicator_concentric
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E D Ω : Set (Space d)}
    (hmin : ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E) (hD : MeasurableSet D)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {x₀ : Space d} {r₀ r_hi : ℝ} (hr₀ : 0 ≤ r₀) (hr : r₀ < r_hi)
    (hsub : closedBall x₀ r_hi ⊆ Ω)
    (hED : ∀ᵐ x ∂volume, x ∉ closedBall x₀ r₀ → (x ∈ E ↔ x ∈ D)) :
    variationalPerimeter b E (ball x₀ r_hi) ≤ variationalPerimeter b D (ball x₀ r_hi) := by
  by_cases hPD : variationalPerimeter b D (ball x₀ r_hi) = ⊤
  · rw [hPD]
    exact le_top
  have hr_hi_pos : 0 < r_hi := hr₀.trans_lt hr
  obtain ⟨φ, s, err, hφ, hs_mem, herr_lim, hmin_φ, hcomp_k⟩ :=
    exists_subsequence_radius_perimeter_ball_le_add_error hd b hmin hE hD hr₀ hr hsub hPD hED
      (ht (closedBall x₀ r_hi) (isCompact_closedBall x₀ r_hi) hsub)
  have hlsc_s : variationalPerimeter b E (ball x₀ s) ≤
      liminf (fun k ↦ variationalPerimeter b (E_seq (φ k)) (ball x₀ s)) atTop := by
    refine variationalPerimeter_le_liminf b (fun k ↦ E_seq (φ k)) E (ball x₀ s)
      (fun k ↦ (hmin_φ k).measurableSet) hE fun K hK hKs ↦ ?_
    have hKΩ : K ⊆ Ω :=
      hKs.trans (((ball_subset_ball hs_mem.2.le).trans ball_subset_closedBall).trans hsub)
    exact (ht K hK hKΩ).comp hφ.tendsto_atTop
  have hrhs_lim : Tendsto (fun k ↦ variationalPerimeter b D (ball x₀ s) + err k) atTop
      (𝓝 (variationalPerimeter b D (ball x₀ s))) := by
    simpa only [add_zero] using tendsto_const_nhds.add herr_lim
  have hcomp_s : variationalPerimeter b E (ball x₀ s) ≤ variationalPerimeter b D (ball x₀ s) := by
    calc
      variationalPerimeter b E (ball x₀ s) ≤
          liminf (fun k ↦ variationalPerimeter b (E_seq (φ k)) (ball x₀ s)) atTop := hlsc_s
      _ ≤ liminf (fun k ↦ variationalPerimeter b D (ball x₀ s) + err k) atTop :=
          liminf_le_liminf (Eventually.of_forall hcomp_k)
      _ = variationalPerimeter b D (ball x₀ s) := hrhs_lim.liminf_eq
  have hPE : variationalPerimeter b E (ball x₀ r_hi) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (variationalPerimeter_ball_le_of_eventually_tendsto_indicator hd b hmin hE ht hr_hi_pos hsub)
  exact perimeter_comparison_localize_of_compact_perturbation b hE hD
    (isCompact_closedBall x₀ r₀) isOpen_ball isOpen_ball
    (closedBall_subset_ball hs_mem.1) (closedBall_subset_ball hr)
    (ne_top_of_le_ne_top hPE (variationalPerimeter_mono b E (ball_subset_ball hs_mem.2.le)))
    hED hcomp_s

/-- Concentric-ball comparison for an `L¹_loc(Ω)` limit of local perimeter minimizers. -/
theorem variationalPerimeter_ball_le_of_tendsto_indicator_concentric
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E D Ω : Set (Space d)}
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E) (hD : MeasurableSet D)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {x₀ : Space d} {r₀ r_hi : ℝ} (hr₀ : 0 ≤ r₀) (hr : r₀ < r_hi)
    (hsub : closedBall x₀ r_hi ⊆ Ω)
    (hED : ∀ᵐ x ∂volume, x ∉ closedBall x₀ r₀ → (x ∈ E ↔ x ∈ D)) :
    variationalPerimeter b E (ball x₀ r_hi) ≤ variationalPerimeter b D (ball x₀ r_hi) :=
  variationalPerimeter_ball_le_of_eventually_tendsto_indicator_concentric hd b
    (Eventually.of_forall hmin) hE hD ht hr₀ hr hsub hED

/-- Stability of `IsLocalPerimeterMinimizer` under `L¹_loc(Ω)` indicator convergence on any open
domain `Ω` where every compact subset lies in a concentric ball pair inside `Ω`
(assuming eventual minimality of `E_seq`). -/
theorem isLocalPerimeterMinimizer_of_eventually_tendsto_indicator
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E Ω : Set (Space d)}
    (hΩ : IsOpen Ω)
    (hcover : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ x₀ r s, 0 < r ∧ r < s ∧ K ⊆ ball x₀ r ∧ closedBall x₀ s ⊆ Ω)
    (hmin : ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0)) :
    IsLocalPerimeterMinimizer b E Ω where
  measurableSet := hE
  isOpen_domain := hΩ
  perimeter_ball_ne_top x₀ r hr hsub :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (variationalPerimeter_ball_le_of_eventually_tendsto_indicator hd b hmin hE ht hr hsub)
  minimizes U D K hU hUΩ hD hK hKU hED := by
    obtain ⟨x₀, r₀, s, hr₀, hr₀s, hKr₀, hsub_s⟩ := hcover K hK (hKU.trans hUΩ)
    have hED_ball : ∀ᵐ x ∂volume, x ∉ closedBall x₀ r₀ → (x ∈ E ↔ x ∈ D) := by
      filter_upwards [hED] with x hx hxnot
      exact hx fun hxK ↦ hxnot (ball_subset_closedBall (hKr₀ hxK))
    have hcomp_s := variationalPerimeter_ball_le_of_eventually_tendsto_indicator_concentric
      hd b hmin hE hD ht hr₀.le hr₀s hsub_s hED_ball
    have hPE_s : variationalPerimeter b E (ball x₀ s) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (variationalPerimeter_ball_le_of_eventually_tendsto_indicator hd b hmin hE ht
          (hr₀.trans hr₀s) hsub_s)
    exact perimeter_comparison_localize_of_compact_perturbation b hE hD hK isOpen_ball hU
      (hKr₀.trans (ball_subset_ball hr₀s.le)) hKU hPE_s hED hcomp_s

/-- Stability of `IsLocalPerimeterMinimizer` under `L¹_loc(Ω)` indicator convergence on any open
domain `Ω` satisfying the concentric-ball compact cover property. -/
theorem isLocalPerimeterMinimizer_of_tendsto_indicator
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E Ω : Set (Space d)}
    (hcover : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ x₀ r s, 0 < r ∧ r < s ∧ K ⊆ ball x₀ r ∧ closedBall x₀ s ⊆ Ω)
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0)) :
    IsLocalPerimeterMinimizer b E Ω :=
  isLocalPerimeterMinimizer_of_eventually_tendsto_indicator hd b (hmin 0).isOpen_domain hcover
    (Eventually.of_forall hmin) hE ht

/-- Stability of `IsLocalPerimeterMinimizer` on `ball c₀ R₀` (`0 < R₀`) under `L¹_loc`
indicator convergence of eventually minimal phases. -/
theorem isLocalPerimeterMinimizer_ball_of_eventually_tendsto_indicator
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E : Set (Space d)}
    {c₀ : Space d} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hmin : ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) (ball c₀ R₀))
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ ball c₀ R₀ →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0)) :
    IsLocalPerimeterMinimizer b E (ball c₀ R₀) := by
  refine isLocalPerimeterMinimizer_of_eventually_tendsto_indicator hd b isOpen_ball ?_ hmin hE ht
  intro K hK hKsub
  obtain ⟨r₁, r₂, hr₁, hr₁₂, hr₂R₀, hKB⟩ := exists_radii_lt_subset_ball_of_isCompact hR₀ hK hKsub
  exact ⟨c₀, r₁, r₂, hr₁, hr₁₂, hKB, closedBall_subset_ball hr₂R₀⟩

/-- Stability of `IsLocalPerimeterMinimizer` on `ball c₀ R₀` (`0 < R₀`) under `L¹_loc`
indicator convergence. -/
theorem isLocalPerimeterMinimizer_ball_of_tendsto_indicator
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E : Set (Space d)}
    {c₀ : Space d} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E_seq j) (ball c₀ R₀))
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ ball c₀ R₀ →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0)) :
    IsLocalPerimeterMinimizer b E (ball c₀ R₀) :=
  isLocalPerimeterMinimizer_ball_of_eventually_tendsto_indicator hd b hR₀
    (Eventually.of_forall hmin) hE ht

/-- Stability of `IsLocalPerimeterMinimizer` on `univ` under `L¹_loc` indicator convergence of
eventually minimal phases. -/
theorem isLocalPerimeterMinimizer_univ_of_eventually_tendsto_indicator
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E : Set (Space d)}
    (hmin : ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) univ)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0)) :
    IsLocalPerimeterMinimizer b E univ := by
  refine isLocalPerimeterMinimizer_of_eventually_tendsto_indicator hd b isOpen_univ ?_ hmin hE
    fun K hK _ ↦ ht K hK
  intro K hK _
  obtain ⟨n, hn⟩ := compact_subset_perimeter_ball hK
  exact ⟨0, (n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith, hn, subset_univ _⟩

/-- Stability of `IsLocalPerimeterMinimizer` on `univ` under `L¹_loc` indicator convergence. -/
theorem isLocalPerimeterMinimizer_univ_of_tendsto_indicator
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E : Set (Space d)}
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E_seq j) univ)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0)) :
    IsLocalPerimeterMinimizer b E univ :=
  isLocalPerimeterMinimizer_univ_of_eventually_tendsto_indicator hd b
    (Eventually.of_forall hmin) hE ht

/-! ### 4. Continuity-ball perimeter convergence (BV8) -/

/-- For any locally finite measure `μ` on `Space d` and any `r : ℝ`, `μ (ball x₀ s)` converges
as `s → r+` to `μ (closedBall x₀ r)`. -/
theorem tendsto_measure_ball_nhdsGT_closedBall {d : ℕ} (μ : Measure (Space d))
    [IsLocallyFiniteMeasure μ] (x₀ : Space d) (r : ℝ) :
    Tendsto (fun s ↦ μ (ball x₀ s)) (𝓝[>] r) (𝓝 (μ (closedBall x₀ r))) := by
  let s_seq : ℕ → ℝ := fun k ↦ r + 1 / ((k : ℝ) + 1)
  have hs_gt (k : ℕ) : r < s_seq k := by
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    dsimp [s_seq]
    linarith
  have hs_anti : Antitone s_seq := fun k l hkl ↦ by
    dsimp [s_seq]
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hkl' : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkl 1
    linarith [div_le_div_of_nonneg_left zero_le_one hkpos hkl']
  have hs_lim : Tendsto s_seq atTop (𝓝 r) := by
    have h0 := (tendsto_const_nhds (x := r)).add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [s_seq, add_zero] using h0
  have hiInter : (⋂ k : ℕ, ball x₀ (s_seq k)) = closedBall x₀ r := by
    ext x
    simp only [mem_iInter, mem_ball, mem_closedBall]
    constructor
    · intro hx
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hs_lim
        (Eventually.of_forall fun k ↦ (hx k).le)
    · intro hx k
      exact hx.trans_lt (hs_gt k)
  have hseq_lim : Tendsto (fun k ↦ μ (ball x₀ (s_seq k))) atTop (𝓝 (μ (closedBall x₀ r))) := by
    rw [← hiInter]
    refine tendsto_measure_iInter_atTop (fun _ ↦ measurableSet_ball.nullMeasurableSet)
      (fun k l hkl ↦ ball_subset_ball (hs_anti hkl)) ⟨0, ?_⟩
    exact ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall x₀ (s_seq 0)).measure_lt_top).ne
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with s (hs : r < s)
    exact ha.trans_le (measure_mono (closedBall_subset_ball hs))
  · intro M hM
    obtain ⟨k, hk⟩ := (hseq_lim.eventually (gt_mem_nhds hM)).exists
    filter_upwards [Ioo_mem_nhdsGT (hs_gt k)] with s hs
    exact (measure_mono (ball_subset_ball hs.2.le)).trans_lt hk

/-- Zero sphere mass for a local Radon representation `μ` on `ball x₀ (r + δ)` is equivalent to
right-continuity of `s ↦ variationalPerimeter b E (ball x₀ s)` at `r`. -/
theorem sphere_measure_eq_zero_iff_tendsto_variationalPerimeter_ball {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)}
    (μ : Measure (Space d)) [IsLocallyFiniteMeasure μ]
    {x₀ : Space d} {r δ : ℝ} (hδ : 0 < δ)
    (hμ : ∀ U, IsOpen U → U ⊆ ball x₀ (r + δ) → μ U = variationalPerimeter b E U) :
    μ (sphere x₀ r) = 0 ↔
      Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
        (𝓝 (variationalPerimeter b E (ball x₀ r))) := by
  have hright_μ : Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
      (𝓝 (μ (closedBall x₀ r))) := by
    refine (tendsto_measure_ball_nhdsGT_closedBall μ x₀ r).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by linarith : r < r + δ)] with s hs
    exact hμ (ball x₀ s) isOpen_ball (ball_subset_ball hs.2.le)
  have hball_eq : μ (ball x₀ r) = variationalPerimeter b E (ball x₀ r) :=
    hμ (ball x₀ r) isOpen_ball (ball_subset_ball (by linarith))
  have hunion : closedBall x₀ r = ball x₀ r ∪ sphere x₀ r := by
    ext x
    simp only [mem_closedBall, mem_union, mem_ball, mem_sphere]
    exact le_iff_lt_or_eq
  have hdisj : Disjoint (ball x₀ r) (sphere x₀ r) :=
    disjoint_left.mpr fun x hxb hxs ↦ (mem_ball.mp hxb).ne (mem_sphere.mp hxs)
  have hclosed_split : μ (closedBall x₀ r) = μ (ball x₀ r) + μ (sphere x₀ r) := by
    rw [hunion, measure_union hdisj isClosed_sphere.measurableSet]
  have hball_ne_top : μ (ball x₀ r) ≠ ⊤ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x₀ r).measure_lt_top).ne
  constructor
  · intro hsph
    have heq : μ (closedBall x₀ r) = variationalPerimeter b E (ball x₀ r) := by
      rw [hclosed_split, hsph, add_zero, hball_eq]
    rwa [← heq]
  · intro hlim
    have heq : μ (closedBall x₀ r) = variationalPerimeter b E (ball x₀ r) :=
      tendsto_nhds_unique hright_μ hlim
    rw [hclosed_split, ← hball_eq] at heq
    have heq' : μ (ball x₀ r) + μ (sphere x₀ r) = μ (ball x₀ r) + 0 := by
      rwa [add_zero]
    exact (ENNReal.add_right_inj hball_ne_top).mp heq'

/-- Continuity-ball perimeter convergence (BV8, right-continuity form, eventual minimality):
whenever `s ↦ P(E, ball x₀ s)` is right-continuous at `r` (`0 < r`, `closedBall x₀ r ⊆ Ω`),
`P(E_seq j, ball x₀ r) → P(E, ball x₀ r)` as `j → ∞`. -/
theorem tendsto_variationalPerimeter_ball_of_eventually_right_continuous
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E Ω : Set (Space d)}
    (hmin : ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {x₀ : Space d} {r : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hcont : Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
      (𝓝 (variationalPerimeter b E (ball x₀ r)))) :
    Tendsto (fun j ↦ variationalPerimeter b (E_seq j) (ball x₀ r)) atTop
      (𝓝 (variationalPerimeter b E (ball x₀ r))) := by
  obtain ⟨j₀, hj₀⟩ := hmin.exists
  have hΩ : IsOpen Ω := hj₀.isOpen_domain
  obtain ⟨δ, hδ, hsub_δ⟩ := exists_pos_closedBall_add_subset_open hΩ hsub
  let L := variationalPerimeter b E (ball x₀ r)
  have hlsc : L ≤ liminf (fun j ↦ variationalPerimeter b (E_seq j) (ball x₀ r)) atTop :=
    variationalPerimeter_le_liminf_of_eventually_measurable b
      (hmin.mono fun _ h ↦ h.measurableSet) hE
      (fun K hK hKb ↦ ht K hK (hKb.trans (ball_subset_closedBall.trans hsub)))
  rw [tendsto_order]
  constructor
  · intro a ha
    exact eventually_lt_of_lt_liminf (ha.trans_le hlsc)
  · intro M hLM
    by_contra hnot
    have hfreq : ∃ᶠ j in atTop, M ≤ variationalPerimeter b (E_seq j) (ball x₀ r) := by
      simpa only [Filter.not_eventually, not_lt] using hnot
    obtain ⟨ψ, hψ, hψ_ge⟩ := Filter.extraction_of_frequently_atTop hfreq
    have hnear : ∀ᶠ s in 𝓝[>] r,
        s ∈ Ioo r (r + δ) ∧ variationalPerimeter b E (ball x₀ s) < M := by
      filter_upwards [Ioo_mem_nhdsGT (by linarith : r < r + δ),
        hcont.eventually (gt_mem_nhds hLM)] with s hs1 hs2
      exact ⟨hs1, hs2⟩
    obtain ⟨r_hi, hr_hi_mem, hPr_hi_lt⟩ := hnear.exists
    have hr_hi_pos : 0 < r_hi := hr.trans hr_hi_mem.1
    have hsub_hi : closedBall x₀ r_hi ⊆ Ω :=
      (closedBall_subset_closedBall hr_hi_mem.2.le).trans hsub_δ
    have hPE_hi : variationalPerimeter b E (ball x₀ r_hi) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (variationalPerimeter_ball_le_of_eventually_tendsto_indicator hd b hmin hE ht
          hr_hi_pos hsub_hi)
    have hmin_ψ : ∀ᶠ m in atTop, IsLocalPerimeterMinimizer b (E_seq (ψ m)) Ω :=
      hψ.tendsto_atTop.eventually hmin
    have ht_ψ : Tendsto (fun m ↦ ∫ x in closedBall x₀ r_hi,
        ‖(E_seq (ψ m)).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0) :=
      (ht (closedBall x₀ r_hi) (isCompact_closedBall x₀ r_hi) hsub_hi).comp hψ.tendsto_atTop
    obtain ⟨φ, s, err, -, hs_mem, herr_lim, -, hcomp_k⟩ :=
      exists_subsequence_radius_perimeter_ball_le_add_error hd b hmin_ψ hE hE
        hr.le hr_hi_mem.1 hsub_hi hPE_hi (Eventually.of_forall fun _ _ ↦ Iff.rfl) ht_ψ
    have hrhs_lim : Tendsto (fun k ↦ variationalPerimeter b E (ball x₀ r_hi) + err k) atTop
        (𝓝 (variationalPerimeter b E (ball x₀ r_hi))) := by
      simpa only [add_zero] using tendsto_const_nhds.add herr_lim
    obtain ⟨k, hk⟩ := (hrhs_lim.eventually (gt_mem_nhds hPr_hi_lt)).exists
    have hle_k : M ≤ variationalPerimeter b E (ball x₀ r_hi) + err k := by
      calc
        M ≤ variationalPerimeter b (E_seq (ψ (φ k))) (ball x₀ r) := hψ_ge (φ k)
        _ ≤ variationalPerimeter b (E_seq (ψ (φ k))) (ball x₀ s) :=
            variationalPerimeter_mono b _ (ball_subset_ball hs_mem.1.le)
        _ ≤ variationalPerimeter b E (ball x₀ s) + err k := hcomp_k k
        _ ≤ variationalPerimeter b E (ball x₀ r_hi) + err k :=
            add_le_add (variationalPerimeter_mono b E (ball_subset_ball hs_mem.2.le)) le_rfl
    exact not_lt_of_ge hle_k hk

/-- Real-valued continuity-ball perimeter convergence (right-continuity form, eventual minimality). -/
theorem tendsto_variationalPerimeter_ball_toReal_of_eventually_right_continuous
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E Ω : Set (Space d)}
    (hmin : ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {x₀ : Space d} {r : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hcont : Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
      (𝓝 (variationalPerimeter b E (ball x₀ r)))) :
    Tendsto (fun j ↦ (variationalPerimeter b (E_seq j) (ball x₀ r)).toReal) atTop
      (𝓝 ((variationalPerimeter b E (ball x₀ r)).toReal)) := by
  have hPE_ne_top : variationalPerimeter b E (ball x₀ r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (variationalPerimeter_ball_le_of_eventually_tendsto_indicator hd b hmin hE ht hr hsub)
  exact (ENNReal.tendsto_toReal hPE_ne_top).comp
    (tendsto_variationalPerimeter_ball_of_eventually_right_continuous hd b hmin hE ht hr hsub hcont)

/-- Continuity-ball perimeter convergence (BV8, right-continuity form). -/
theorem tendsto_variationalPerimeter_ball_of_right_continuous
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E Ω : Set (Space d)}
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {x₀ : Space d} {r : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hcont : Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
      (𝓝 (variationalPerimeter b E (ball x₀ r)))) :
    Tendsto (fun j ↦ variationalPerimeter b (E_seq j) (ball x₀ r)) atTop
      (𝓝 (variationalPerimeter b E (ball x₀ r))) :=
  tendsto_variationalPerimeter_ball_of_eventually_right_continuous hd b
    (Eventually.of_forall hmin) hE ht hr hsub hcont

/-- Real-valued continuity-ball perimeter convergence (BV8, right-continuity form). -/
theorem tendsto_variationalPerimeter_ball_toReal_of_right_continuous
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E Ω : Set (Space d)}
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {x₀ : Space d} {r : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω)
    (hcont : Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
      (𝓝 (variationalPerimeter b E (ball x₀ r)))) :
    Tendsto (fun j ↦ (variationalPerimeter b (E_seq j) (ball x₀ r)).toReal) atTop
      (𝓝 ((variationalPerimeter b E (ball x₀ r)).toReal)) :=
  tendsto_variationalPerimeter_ball_toReal_of_eventually_right_continuous hd b
    (Eventually.of_forall hmin) hE ht hr hsub hcont

/-- Continuity-ball perimeter convergence (BV8, zero sphere-mass form, eventual minimality). -/
theorem tendsto_variationalPerimeter_ball_of_eventually_sphere_zero
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E Ω : Set (Space d)}
    (hmin : ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {x₀ : Space d} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hsub : closedBall x₀ r ⊆ Ω)
    (μ : Measure (Space d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ ball x₀ (r + δ) → μ U = variationalPerimeter b E U)
    (hsph : μ (sphere x₀ r) = 0) :
    Tendsto (fun j ↦ variationalPerimeter b (E_seq j) (ball x₀ r)) atTop
      (𝓝 (variationalPerimeter b E (ball x₀ r))) :=
  tendsto_variationalPerimeter_ball_of_eventually_right_continuous hd b hmin hE ht hr hsub
    ((sphere_measure_eq_zero_iff_tendsto_variationalPerimeter_ball b μ hδ hμ).mp hsph)

/-- Continuity-ball perimeter convergence (BV8, zero sphere-mass form). -/
theorem tendsto_variationalPerimeter_ball_of_sphere_zero
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E Ω : Set (Space d)}
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {x₀ : Space d} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hsub : closedBall x₀ r ⊆ Ω)
    (μ : Measure (Space d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ ball x₀ (r + δ) → μ U = variationalPerimeter b E U)
    (hsph : μ (sphere x₀ r) = 0) :
    Tendsto (fun j ↦ variationalPerimeter b (E_seq j) (ball x₀ r)) atTop
      (𝓝 (variationalPerimeter b E (ball x₀ r))) :=
  tendsto_variationalPerimeter_ball_of_eventually_sphere_zero hd b
    (Eventually.of_forall hmin) hE ht hr hδ hsub μ hμ hsph

/-- Real-valued continuity-ball perimeter convergence (BV8, zero sphere-mass form). -/
theorem tendsto_variationalPerimeter_ball_toReal_of_sphere_zero
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E_seq : ℕ → Set (Space d)} {E Ω : Set (Space d)}
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E_seq j) Ω)
    (hE : MeasurableSet E)
    (ht : ∀ K : Set (Space d), IsCompact K → K ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq j).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0))
    {x₀ : Space d} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hsub : closedBall x₀ r ⊆ Ω)
    (μ : Measure (Space d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ ball x₀ (r + δ) → μ U = variationalPerimeter b E U)
    (hsph : μ (sphere x₀ r) = 0) :
    Tendsto (fun j ↦ (variationalPerimeter b (E_seq j) (ball x₀ r)).toReal) atTop
      (𝓝 ((variationalPerimeter b E (ball x₀ r)).toReal)) :=
  tendsto_variationalPerimeter_ball_toReal_of_eventually_right_continuous hd b
    (Eventually.of_forall hmin) hE ht hr hsub
    ((sphere_measure_eq_zero_iff_tendsto_variationalPerimeter_ball b μ hδ hμ).mp hsph)

/-! ### 5. BV subsequence compactness for measurable phases and local perimeter minimizers -/

/-- Uniform Lipschitz bound on `closedBall 0 r` for fixed-scale mollifications of arbitrary
measurable phase indicators. -/
theorem mollify_phaseIndicator_lipschitzOn {d : ℕ} (n : ℕ) (r : ℝ) :
    ∃ C : NNReal, ∀ A : Set (Space d), MeasurableSet A →
      LipschitzOnWith C (mollify (A.indicator (fun _ ↦ (1 : ℝ))) n) (closedBall 0 r) := by
  let k := (averagingBump d n).normed volume
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    ((averagingBump d n).hasCompactSupport_normed (μ := volume))
    ((averagingBump d n).contDiff_normed (n := (1 : ℕ∞))) (by simp)
  let V := volume.real (closedBall (0 : Space d) (r + 1))
  refine ⟨⟨(L : ℝ) * V, mul_nonneg L.coe_nonneg measureReal_nonneg⟩,
    fun A hA ↦ lipschitzOnWith_iff_dist_le_mul.mpr fun x hx y hy ↦ ?_⟩
  let v := A.indicator (fun _ ↦ (1 : ℝ))
  have hv_loc : LocallyIntegrable v volume := locallyIntegrable_phaseIndicator hA
  have hv_le (t : Space d) : ‖v t‖ ≤ 1 := by
    by_cases ht : t ∈ A <;> simp [v, ht]
  have hi (z : Space d) : Integrable (fun t ↦ k (z - t) * v t) := by
    have hh := ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_right
      (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ).flip hv_loc
      ((averagingBump d n).continuous_normed (μ := volume)) z
    exact hh.integrable
  have he (z : Space d) : mollify v n z = ∫ t, k (z - t) * v t :=
    MeasureTheory.convolution_eq_swap (ContinuousLinearMap.lsmul ℝ ℝ)
  rw [dist_eq_norm, he x, he y, ← integral_sub (hi x) (hi y)]
  have hz (z : Space d) (hz : z ∈ closedBall 0 r) (t : Space d)
      (ht : t ∉ closedBall 0 (r + 1)) : k (z - t) = 0 := by
    apply Function.notMem_support.mp
    rw [(averagingBump d n).support_normed_eq]
    intro hb
    have hzt : ‖z - t‖ < (averagingBump d n).rOut := by simpa using hb
    have hz' : ‖z‖ ≤ r := by simpa using hz
    have ht' : r + 1 < ‖t‖ := by simpa using ht
    have hn := norm_sub_le z (z - t)
    rw [sub_sub_cancel] at hn
    linarith [averagingBump_rOut_le_one d n]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := closedBall (0 : Space d) (r + 1)) (fun t ht ↦ by
      rw [hz x hx t ht, hz y hy t ht]; simp)]
  have hb := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := closedBall (0 : Space d) (r + 1))
    (C := (L : ℝ) * dist x y)
    (f := fun t ↦ k (x - t) * v t - k (y - t) * v t)
    (isCompact_closedBall (0 : Space d) (r + 1)).measure_lt_top
    (fun t _ ↦ ?_)
  · calc
      _ ≤ ((L : ℝ) * dist x y) * V := hb
      _ = _ := by change _ = ((L : ℝ) * V) * dist x y; ring
  · rw [← sub_mul, norm_mul]
    have hxy : ‖k (x - t) - k (y - t)‖ ≤ (L : ℝ) * dist x y := by
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hL.dist_le_mul (x - t) (y - t)
    exact (mul_le_mul hxy (hv_le t) (norm_nonneg _)
      (mul_nonneg L.coe_nonneg dist_nonneg)).trans_eq (mul_one _)

/-- Quantitative `L¹` mollification error for a measurable phase indicator from a perimeter bound
on an enlarged ball `ball 0 R` (`r + 1 / (n + 1) < R`). -/
theorem integral_norm_mollify_phaseIndicator_sub_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {A : Set (Space d)} (hA : MeasurableSet A)
    (n : ℕ) {r R B : ℝ} (hrR : r + 1 / ((n : ℝ) + 1) < R) (hB : 0 ≤ B)
    (hP : variationalPerimeter b A (ball 0 R) ≤ ENNReal.ofReal B) :
    (∫ x in closedBall 0 r,
      ‖mollify (A.indicator (fun _ ↦ (1 : ℝ))) n x - A.indicator (fun _ ↦ (1 : ℝ)) x‖) ≤
      (1 / ((n : ℝ) + 1)) * B := by
  let v := A.indicator (fun _ ↦ (1 : ℝ))
  let k := (averagingBump d n).normed volume
  have hv_loc : LocallyIntegrable v volume := locallyIntegrable_phaseIndicator hA
  have hv_meas : Measurable v := measurable_const.indicator hA
  have hpoint (x : Space d) :
      ‖mollify v n x - v x‖ ≤ ∫ t, k t * ‖v (x - t) - v x‖ := by
    have hi : Integrable (fun t ↦ k t * v (x - t)) :=
      (((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
        (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
        (averagingBump d n).continuous_normed hv_loc x).integrable
    have hc : Integrable (fun t ↦ k t * v x) :=
      (averagingBump d n).integrable_normed.mul_const _
    have he : mollify v n x - v x = ∫ t, k t * (v (x - t) - v x) := by
      simp_rw [mul_sub]
      rw [integral_sub hi hc, integral_mul_const, (averagingBump d n).integral_normed, one_mul]
      rfl
    rw [he]
    refine (norm_integral_le_integral_norm (fun t ↦ k t * (v (x - t) - v x))).trans_eq ?_
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    dsimp only
    rw [norm_mul, Real.norm_of_nonneg ((averagingBump d n).nonneg_normed t)]
  let F : Space d → Space d → ℝ := fun x t ↦ k t * ‖v (x - t) - v x‖
  have hF_meas : Measurable F.uncurry :=
    ((averagingBump d n).continuous_normed.measurable.comp measurable_snd).mul
      (((hv_meas.comp (measurable_fst.sub measurable_snd)).sub (hv_meas.comp measurable_fst)).norm)
  obtain ⟨Mk, hMk⟩ := ((averagingBump d n).hasCompactSupport_normed (μ := volume))
    |>.exists_bound_of_continuous (averagingBump d n).continuous_normed
  have hMk_nonneg : 0 ≤ Mk := (norm_nonneg (k 0)).trans (hMk 0)
  have hfi : Integrable F.uncurry
      ((volume.restrict (closedBall 0 r)).prod (volume.restrict (closedBall 0 1))) := by
    let _ : IsFiniteMeasure (volume.restrict (closedBall (0 : Space d) r)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall 0 r).measure_lt_top⟩
    let _ : IsFiniteMeasure (volume.restrict (closedBall (0 : Space d) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall 0 1).measure_lt_top⟩
    refine Integrable.of_bound hF_meas.aestronglyMeasurable (Mk * 2)
      (Eventually.of_forall fun p ↦ ?_)
    have hv1 : v (p.1 - p.2) ∈ Icc (0 : ℝ) 1 := by
      by_cases h1 : p.1 - p.2 ∈ A <;> simp [v, h1]
    have hv2 : v p.1 ∈ Icc (0 : ℝ) 1 := by
      by_cases h2 : p.1 ∈ A <;> simp [v, h2]
    have hdiff : ‖v (p.1 - p.2) - v p.1‖ ≤ 2 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hv1.1, hv2.2], by linarith [hv1.2, hv2.1]⟩
    calc
      ‖F.uncurry p‖ = ‖k p.2‖ * ‖v (p.1 - p.2) - v p.1‖ := by
        change ‖k p.2 * ‖v (p.1 - p.2) - v p.1‖‖ = _
        rw [norm_mul, norm_norm]
      _ ≤ Mk * 2 := mul_le_mul (hMk p.2) hdiff (norm_nonneg _) hMk_nonneg
  have he (x : Space d) : (∫ t, F x t) = ∫ t in closedBall 0 1, F x t := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    simp only [F, k, averagingBump_normed_zero_of_notMem_unitBall ht, zero_mul]
  have hsub_int : IntegrableOn (fun x ↦ ‖mollify v n x - v x‖) (closedBall 0 r) volume := by
    have hcont := (mollify_contDiff_of_locallyIntegrable hv_loc n).continuous
    have hm_int : IntegrableOn (mollify v n) (closedBall 0 r) volume :=
      hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)
    have hv_int : IntegrableOn v (closedBall 0 r) volume :=
      (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator hA
    exact (hm_int.sub hv_int).norm
  have hle : (∫ x in closedBall 0 r, ‖mollify v n x - v x‖) ≤
      ∫ x in closedBall 0 r, ∫ t in closedBall 0 1, F x t := by
    refine integral_mono hsub_int hfi.integral_prod_left fun x ↦ ?_
    rw [← he x]
    exact hpoint x
  rw [integral_integral_swap hfi] at hle
  let err_n : ℝ := (1 / ((n : ℝ) + 1)) * B
  have hk_int : IntegrableOn (fun t : Space d ↦ k t * err_n) (closedBall 0 1) volume :=
    (((averagingBump d n).continuous_normed.mul continuous_const).continuousOn)
      |>.integrableOn_compact (isCompact_closedBall 0 1)
  have hb : (∫ t in closedBall 0 1, ∫ x in closedBall 0 r, F x t) ≤
      ∫ t in closedBall 0 1, k t * err_n := by
    refine setIntegral_mono_on hfi.integral_prod_right hk_int isClosed_closedBall.measurableSet
      fun t _ ↦ ?_
    change (∫ x in closedBall 0 r, k t * ‖v (x - t) - v x‖) ≤ k t * err_n
    rw [integral_const_mul]
    by_cases ht' : t ∈ ball (0 : Space d) (averagingBump d n).rOut
    · have ht_lt : ‖t‖ < 1 / ((n : ℝ) + 1) := by simpa [averagingBump] using ht'
      have ht_R : r + ‖-t‖ < R := by
        rw [norm_neg]
        linarith
      have htrans := integral_phase_translation_le_perimeter_bound b hA (-t) ht_R hB hP
      simp only [norm_neg, ← sub_eq_add_neg] at htrans
      have htrans' : (∫ x in closedBall 0 r, ‖v (x - t) - v x‖) ≤ err_n :=
        htrans.trans (mul_le_mul_of_nonneg_right ht_lt.le hB)
      exact mul_le_mul_of_nonneg_left htrans' ((averagingBump d n).nonneg_normed t)
    · have hz : k t = 0 := Function.notMem_support.mp
        (by simpa only [k, (averagingBump d n).support_normed_eq] using ht')
      simp [hz]
  have hmass : (∫ t in closedBall 0 1, k t) = 1 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht ↦ averagingBump_normed_zero_of_notMem_unitBall ht)]
    exact (averagingBump d n).integral_normed
  rw [integral_mul_const, hmass, one_mul] at hb
  exact hle.trans hb

/-- Variant of `integral_cauchy_of_approximations` where the approximation error bound holds
eventually in the sequence index `j` for each fixed smoothing index `n`. -/
theorem integral_cauchy_of_eventually_approximations {d : ℕ} {K : Set (Space d)}
    (F : ℕ → Space d → ℝ) (G : ℕ → ℕ → Space d → ℝ) (δ : ℕ → ℝ)
    (hF : ∀ j, IntegrableOn (F j) K) (hG : ∀ n j, IntegrableOn (G n j) K)
    (hδ : Tendsto δ atTop (𝓝 0))
    (herr : ∀ n, ∀ᶠ j in atTop, (∫ x in K, ‖F j x - G n j x‖) ≤ δ n)
    (hc : ∀ n ε, 0 < ε → ∃ N, ∀ j ≥ N, ∀ k ≥ N,
      (∫ x in K, ‖G n j x - G n k x‖) < ε) :
    ∀ ε, 0 < ε → ∃ N, ∀ j ≥ N, ∀ k ≥ N, (∫ x in K, ‖F j x - F k x‖) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := (hδ.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (herr n)
  obtain ⟨N₂, hN₂⟩ := hc n (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun j hj k hk ↦ ?_⟩
  have hj1 : N₁ ≤ j := (le_max_left _ _).trans hj
  have hk1 : N₁ ≤ k := (le_max_left _ _).trans hk
  have hj2 : N₂ ≤ j := (le_max_right _ _).trans hj
  have hk2 : N₂ ≤ k := (le_max_right _ _).trans hk
  have h1 := integral_norm_sub_triangle (hF j) (hG n j) (hF k)
  have h2 := integral_norm_sub_triangle (hG n j) (hG n k) (hF k)
  have hs : (∫ x in K, ‖G n k x - F k x‖) = ∫ x in K, ‖F k x - G n k x‖ := by
    simp_rw [norm_sub_rev (G n k _) (F k _)]
  rw [hs] at h2
  linarith [hN₁ j hj1, hN₁ k hk1, hN₂ j hj2 k hk2]

/-- Clamping any real number `y` into `[0, 1]` does not increase its distance to `u ∈ [0, 1]`. -/
theorem norm_sub_clamp_unit_le {u y : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖u - max 0 (min 1 y)‖ ≤ ‖u - y‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rcases lt_or_ge y 0 with hy0 | hy0
  · have hmin : min 1 y = y := min_eq_right (by linarith)
    have hmax : max 0 y = 0 := max_eq_left hy0.le
    rw [hmin, hmax, sub_zero, abs_of_nonneg hu.1, abs_of_nonneg (by linarith [hu.1])]
    linarith
  · rcases le_or_gt y 1 with hy1 | hy1
    · rw [min_eq_right hy1, max_eq_right hy0]
    · rw [min_eq_left hy1.le, max_eq_right zero_le_one,
        abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith [hu.2])]
      linarith

/-- Any `L¹(K)` limit of `[0, 1]`-valued measurable phase indicators on a compact set `K`
takes values in `{0, 1}` almost everywhere on `K`. -/
theorem ae_eq_zero_or_one_of_indicator_integral_limit {d : ℕ}
    {A : ℕ → Set (Space d)} (hA : ∀ j, MeasurableSet (A j))
    {K : Set (Space d)} {w : Space d → ℝ}
    (hK : IsCompact K) (hw_meas : AEStronglyMeasurable w (volume.restrict K))
    (hw_Icc : ∀ x, w x ∈ Icc (0 : ℝ) 1)
    (ht : Tendsto (fun j ↦ ∫ x in K, ‖(A j).indicator (fun _ ↦ (1 : ℝ)) x - w x‖)
      atTop (𝓝 0)) :
    ∀ᵐ x ∂volume.restrict K, w x = 0 ∨ w x = 1 := by
  let _ : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hw_int : IntegrableOn w K volume :=
    Integrable.of_bound hw_meas 1 (Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (hw_Icc x).1]
      exact (hw_Icc x).2)
  have hprod_int : IntegrableOn (fun x ↦ ‖w x * (1 - w x)‖) K volume := by
    refine Integrable.of_bound
      ((hw_meas.mul (aestronglyMeasurable_const.sub hw_meas)).norm) 1
      (Eventually.of_forall fun x ↦ ?_)
    have hx := hw_Icc x
    rw [norm_norm, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2))]
    nlinarith [hx.1, hx.2]
  have hpt (j : ℕ) (x : Space d) :
      ‖w x * (1 - w x)‖ ≤ ‖(A j).indicator (fun _ ↦ (1 : ℝ)) x - w x‖ := by
    have hx := hw_Icc x
    by_cases hxA : x ∈ A j
    · simp only [hxA, indicator_of_mem, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
        abs_of_nonneg (sub_nonneg.mpr hx.2)]
      nlinarith [hx.1, hx.2]
    · simp only [hxA, not_false_eq_true, indicator_of_notMem, zero_sub, norm_neg,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)), abs_of_nonneg hx.1]
      nlinarith [hx.1, hx.2]
  have hint_le : (∫ x in K, ‖w x * (1 - w x)‖) ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall fun j ↦ ?_)
    have hA_int : IntegrableOn ((A j).indicator (fun _ ↦ (1 : ℝ))) K volume :=
      (continuousOn_const.integrableOn_compact hK).indicator (hA j)
    exact integral_mono hprod_int (hA_int.sub hw_int).norm (hpt j)
  have hint_zero : (∫ x in K, ‖w x * (1 - w x)‖) = 0 :=
    le_antisymm hint_le (integral_nonneg fun _ ↦ norm_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun x ↦ norm_nonneg (w x * (1 - w x))) hprod_int).mp hint_zero
  filter_upwards [hae] with x hx
  rcases mul_eq_zero.mp (norm_eq_zero.mp hx) with hw0 | hw1
  · exact Or.inl hw0
  · exact Or.inr (sub_eq_zero.mp hw1).symm

/-- Simultaneous uniform subsequence for countably many mollifications of measurable phase
indicators on an arbitrary countable family of origin-centered closed balls. -/
theorem exists_simultaneous_mollified_phaseIndicator_subsequence {d : ℕ}
    (A : ℕ → Set (Space d)) (hA : ∀ j, MeasurableSet (A j)) (r_fam : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n k : ℕ,
      ∃ v : (closedBall (0 : Space d) (r_fam k)) →ᵇ ℝ,
        TendstoUniformly (fun j (x : closedBall (0 : Space d) (r_fam k)) ↦
          mollify ((A (φ j)).indicator (fun _ ↦ (1 : ℝ))) n x) v atTop := by
  let X (i : ℕ × ℕ) := closedBall (0 : Space d) (r_fam i.2)
  let _ : ∀ i, CompactSpace (X i) := fun i ↦
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space d) (r_fam i.2))
  let G : ∀ i : ℕ × ℕ, ℕ → X i →ᵇ ℝ := fun i j ↦
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x ↦ mollify ((A j).indicator (fun _ ↦ (1 : ℝ))) i.1 x,
        (mollify_contDiff_of_locallyIntegrable
          (locallyIntegrable_phaseIndicator (hA j)) i.1).continuous.comp continuous_subtype_val⟩
  have hC (i : ℕ × ℕ) := mollify_phaseIndicator_lipschitzOn (d := d) i.1 (r_fam i.2)
  choose C hC using hC
  have hCG (i : ℕ × ℕ) (j : ℕ) : LipschitzWith (C i) (G i j) :=
    (hC i (A j) (hA j)).to_restrict
  have hMG (i : ℕ × ℕ) (j : ℕ) (x : X i) : G i j x ∈ Icc (0 : ℝ) 1 :=
    mollify_phaseIndicator_mem_Icc (hA j) i.1 x
  obtain ⟨φ, hφ, hv⟩ := exists_simultaneous_uniform_subsequence G C (fun _ ↦ 1) hCG hMG
  exact ⟨φ, hφ, fun n k ↦ hv (n, k)⟩

/-- Global BV compactness for measurable sets with eventual local perimeter bounds on integer balls. -/
theorem exists_subsequence_indicator_tendsto_of_eventually_perimeter_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (E_seq : ℕ → Set (Space d)) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (hbound : ∀ k : ℕ, ∀ᶠ j in atTop, MeasurableSet (E_seq j) ∧
      variationalPerimeter b (E_seq j) (ball 0 ((k : ℝ) + 3)) ≤ ENNReal.ofReal (C k)) :
    ∃ (φ : ℕ → ℕ) (E : Set (Space d)), StrictMono φ ∧ MeasurableSet E ∧
      ∀ K : Set (Space d), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K,
          ‖(E_seq (φ j)).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0) := by
  classical
  let A : ℕ → Set (Space d) := fun j ↦ if MeasurableSet (E_seq j) then E_seq j else ∅
  have hA_meas (j : ℕ) : MeasurableSet (A j) := by
    dsimp [A]
    split_ifs with h
    · exact h
    · exact MeasurableSet.empty
  have hA_ev : ∀ᶠ j in atTop, A j = E_seq j := by
    filter_upwards [hbound 0] with j hj
    simp [A, hj.1]
  let r_fam : ℕ → ℝ := fun k ↦ (k : ℝ) + 1
  obtain ⟨φ, hφ, hlim⟩ := exists_simultaneous_mollified_phaseIndicator_subsequence A hA_meas r_fam
  let F : ℕ → Space d → ℝ := fun j ↦ (A (φ j)).indicator (fun _ ↦ (1 : ℝ))
  have hFi (j k : ℕ) : IntegrableOn (F j) (closedBall 0 (r_fam k)) volume :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 _)).indicator (hA_meas (φ j))
  have hc (k : ℕ) : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N,
      (∫ x in closedBall 0 (r_fam k), ‖F i x - F j x‖) < ε := by
    refine integral_cauchy_of_eventually_approximations F
      (fun n j ↦ mollify (F j) n) (fun n ↦ (1 / ((n : ℝ) + 1)) * C k)
      (fun j ↦ hFi j k)
      (fun n j ↦ (mollify_contDiff_of_locallyIntegrable
        (locallyIntegrable_phaseIndicator (hA_meas (φ j))) n).continuous.continuousOn
          |>.integrableOn_compact (isCompact_closedBall 0 _))
      (by simpa only [zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (C k))
      (fun n ↦ ?_) (fun n ↦ ?_)
    · filter_upwards [hφ.tendsto_atTop.eventually (hbound k)] with j hj
      have hA_eq : A (φ j) = E_seq (φ j) := by simp [A, hj.1]
      have h1_le : 1 / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      have hrR : r_fam k + 1 / ((n : ℝ) + 1) < (k : ℝ) + 3 := by dsimp [r_fam]; linarith
      simp_rw [norm_sub_rev (F j _) (mollify (F j) n _)]
      refine integral_norm_mollify_phaseIndicator_sub_le b (hA_meas (φ j)) n hrR (hC k) ?_
      rw [hA_eq]
      exact hj.2
    · obtain ⟨v, hv⟩ := hlim n k
      exact integral_cauchy_of_uniform_convergence (isCompact_closedBall 0 (r_fam k))
        (fun j ↦ mollify (F j) n)
        (fun j ↦ (mollify_contDiff_of_locallyIntegrable
          (locallyIntegrable_phaseIndicator (hA_meas (φ j))) n).continuous.continuousOn
            |>.integrableOn_compact (isCompact_closedBall 0 _)) v hv
  have hlocal (k : ℕ) : ∃ W : Space d → ℝ, IntegrableOn W (closedBall 0 (r_fam k)) volume ∧
      (∀ x, W x ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫ x in closedBall 0 (r_fam k), ‖F j x - W x‖) atTop (𝓝 0) := by
    obtain ⟨V₀, hV₀, hV₀_lim⟩ :=
      exists_integral_limit_of_cauchy (volume.restrict (closedBall 0 (r_fam k))) F
        (fun j ↦ hFi j k) (hc k)
    let W : Space d → ℝ := fun x ↦ max 0 (min 1 (V₀ x))
    have hW_Icc (x : Space d) : W x ∈ Icc (0 : ℝ) 1 :=
      ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    have hW_meas : AEStronglyMeasurable W (volume.restrict (closedBall 0 (r_fam k))) :=
      aestronglyMeasurable_const.sup (aestronglyMeasurable_const.inf hV₀.aestronglyMeasurable)
    let _ : IsFiniteMeasure (volume.restrict (closedBall (0 : Space d) (r_fam k))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall 0 _).measure_lt_top⟩
    have hW_int : IntegrableOn W (closedBall 0 (r_fam k)) volume :=
      Integrable.of_bound hW_meas 1 (Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hW_Icc x).1]; exact (hW_Icc x).2)
    have hW_lim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r_fam k), ‖F j x - W x‖) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hV₀_lim
        (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun j ↦ ?_
      refine integral_mono ((hFi j k).sub hW_int).norm ((hFi j k).sub hV₀).norm fun x ↦ ?_
      have hFx : F j x ∈ Icc (0 : ℝ) 1 := by
        by_cases hx : x ∈ A (φ j) <;> simp [F, hx]
      exact norm_sub_clamp_unit_le hFx
    exact ⟨W, hW_int, hW_Icc, hW_lim⟩
  choose W hW_int hW_Icc hW_lim using hlocal
  have hcompat (k l : ℕ) (hkl : k ≤ l) :
      W k =ᵐ[volume.restrict (closedBall 0 (r_fam k))] W l := by
    have hs : closedBall (0 : Space d) (r_fam k) ⊆ closedBall 0 (r_fam l) :=
      closedBall_subset_closedBall (by dsimp [r_fam]; exact_mod_cast Nat.add_le_add_right hkl 1)
    exact ae_eq_of_integral_limits F (fun j ↦ hFi j k) (hW_int k) ((hW_int l).mono_set hs)
      (hW_lim k) (integral_limit_mono_set hs F (W l) (fun j ↦ hFi j l) (hW_int l) (hW_lim l))
  have hcover (x : Space d) : ∃ k : ℕ, x ∈ closedBall 0 (r_fam k) := by
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    exact ⟨k, by simp only [mem_closedBall, dist_zero_right, r_fam]; linarith⟩
  obtain ⟨v₀, hv₀⟩ := exists_ae_gluing volume (fun k ↦ closedBall (0 : Space d) (r_fam k))
    (fun _ ↦ measurableSet_closedBall) hcover W hcompat
  let w : Space d → ℝ := fun x ↦ max 0 (min 1 (v₀ x))
  have hw_Icc (x : Space d) : w x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hw_eq (k : ℕ) : w =ᵐ[volume.restrict (closedBall 0 (r_fam k))] W k := by
    filter_upwards [hv₀ k] with x hx
    dsimp [w]
    rw [hx, min_eq_right (hW_Icc k x).2, max_eq_right (hW_Icc k x).1]
  have hw_int (k : ℕ) : IntegrableOn w (closedBall 0 (r_fam k)) volume :=
    (hW_int k).congr (hw_eq k).symm
  have hw_lim (k : ℕ) :
      Tendsto (fun j ↦ ∫ x in closedBall 0 (r_fam k), ‖F j x - w x‖) atTop (𝓝 0) := by
    refine (hW_lim k).congr' (Eventually.of_forall fun j ↦ ?_)
    refine integral_congr_ae ?_
    filter_upwards [hw_eq k] with x hx
    rw [hx]
  have hw_meas : AEStronglyMeasurable w volume := by
    have hm := AEStronglyMeasurable.iUnion fun k ↦ (hw_int k).aestronglyMeasurable
    simpa only [r_fam, iUnion_integer_closedBall, Measure.restrict_univ] using hm
  have hw_two : ∀ᵐ x ∂volume, w x = 0 ∨ w x = 1 := by
    have hloc_two (k : ℕ) : ∀ᵐ x ∂volume.restrict (closedBall 0 (r_fam k)), w x = 0 ∨ w x = 1 :=
      ae_eq_zero_or_one_of_indicator_integral_limit (fun j ↦ hA_meas (φ j))
        (isCompact_closedBall 0 (r_fam k)) (hw_int k).aestronglyMeasurable hw_Icc (hw_lim k)
    have hall := (ae_restrict_iUnion_iff
      (fun k : ℕ ↦ closedBall (0 : Space d) (r_fam k))
      (fun x ↦ w x = 0 ∨ w x = 1)).mpr hloc_two
    simpa only [r_fam, iUnion_integer_closedBall, Measure.restrict_univ] using hall
  obtain ⟨E, hE, hwE⟩ := exists_measurable_indicator_of_two_values hw_meas 1 hw_two
  refine ⟨φ, E, hφ, hE, fun K hK ↦ ?_⟩
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Space d)
  obtain ⟨k, hk⟩ := exists_nat_gt r
  have hs : K ⊆ closedBall 0 (r_fam k) :=
    hr.trans ((ball_subset_ball (by dsimp [r_fam]; linarith)).trans ball_subset_closedBall)
  have hFK : Tendsto (fun j ↦ ∫ x in K, ‖F j x - w x‖) atTop (𝓝 0) :=
    integral_limit_mono_set hs F w (fun j ↦ hFi j k) (hw_int k) (hw_lim k)
  refine hFK.congr' ?_
  filter_upwards [hφ.tendsto_atTop.eventually hA_ev] with j hj
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hwE] with x hx
  dsimp [F]
  rw [hj, hx]

/-- Global blowup/blowdown compactness for families that are eventually local perimeter minimizers
on every origin-centered ball `ball 0 R`: there exists a subsequence converging in `L¹_loc` to a
global perimeter minimizer `E` on `univ`, with continuity-ball perimeter convergence (BV8) at
every ball where the limit perimeter is right-continuous (equivalently, zero sphere mass). -/
theorem exists_subsequence_univ_isLocalPerimeterMinimizer_of_eventually_ball
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (E_seq : ℕ → Set (Space d))
    (hmin : ∀ R : ℝ, 0 < R → ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) (ball 0 R)) :
    ∃ (φ : ℕ → ℕ) (E : Set (Space d)),
      StrictMono φ ∧
      IsLocalPerimeterMinimizer b E univ ∧
      (∀ K : Set (Space d), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K,
          ‖(E_seq (φ j)).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) ∧
      (∀ x₀ : Space d, ∀ r : ℝ, 0 < r →
        Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
          (𝓝 (variationalPerimeter b E (ball x₀ r))) →
        Tendsto (fun j ↦ variationalPerimeter b (E_seq (φ j)) (ball x₀ r)) atTop
          (𝓝 (variationalPerimeter b E (ball x₀ r)))) ∧
      (∀ x₀ : Space d, ∀ r : ℝ, 0 < r →
        ∀ μ : Measure (Space d), IsLocallyFiniteMeasure μ →
          (∀ U, IsOpen U → μ U = variationalPerimeter b E U) →
          μ (sphere x₀ r) = 0 →
          Tendsto (fun j ↦ variationalPerimeter b (E_seq (φ j)) (ball x₀ r)) atTop
            (𝓝 (variationalPerimeter b E (ball x₀ r)))) := by
  let C : ℕ → ℝ := fun k ↦
    ballGluingConstant * (d : ℝ) * volume.real (ball (0 : Space d) 1) * ((k : ℝ) + 3) ^ (d - 1)
  have hC (k : ℕ) : 0 ≤ C k := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg ballGluingConstant_pos.le (Nat.cast_nonneg d)) measureReal_nonneg)
      (pow_nonneg (by positivity) _)
  have hbound (k : ℕ) : ∀ᶠ j in atTop, MeasurableSet (E_seq j) ∧
      variationalPerimeter b (E_seq j) (ball 0 ((k : ℝ) + 3)) ≤ ENNReal.ofReal (C k) := by
    filter_upwards [hmin ((k : ℝ) + 4) (by positivity)] with j hj
    exact ⟨hj.measurableSet, hj.perimeter_ball_le hd (by positivity)
      (closedBall_subset_ball (by linarith))⟩
  obtain ⟨φ, E, hφ, hE, ht⟩ :=
    exists_subsequence_indicator_tendsto_of_eventually_perimeter_bound b E_seq C hC hbound
  have hE_ball (R : ℝ) (hR : 0 < R) : IsLocalPerimeterMinimizer b E (ball 0 R) :=
    isLocalPerimeterMinimizer_ball_of_eventually_tendsto_indicator hd b hR
      (hφ.tendsto_atTop.eventually (hmin R hR)) hE (fun K hK _ ↦ ht K hK)
  have hE_univ : IsLocalPerimeterMinimizer b E univ :=
    isLocalPerimeterMinimizer_univ_of_ball hE_ball
  have hP_cont (x₀ : Space d) (r : ℝ) (hr : 0 < r)
      (hcont : Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
        (𝓝 (variationalPerimeter b E (ball x₀ r)))) :
      Tendsto (fun j ↦ variationalPerimeter b (E_seq (φ j)) (ball x₀ r)) atTop
        (𝓝 (variationalPerimeter b E (ball x₀ r))) := by
    let R : ℝ := ‖x₀‖ + r + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hsub : closedBall x₀ r ⊆ ball 0 R := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm] at hx
      rw [mem_ball, dist_zero_right]
      have htri := norm_add_le (x - x₀) x₀
      rw [sub_add_cancel] at htri
      dsimp [R]
      linarith
    exact tendsto_variationalPerimeter_ball_of_eventually_right_continuous hd b
      (hφ.tendsto_atTop.eventually (hmin R hR)) hE (fun K hK _ ↦ ht K hK) hr hsub hcont
  refine ⟨φ, E, hφ, hE_univ, ht, hP_cont, fun x₀ r hr μ hμ_loc hμ_open hsph ↦ ?_⟩
  let _ : IsLocallyFiniteMeasure μ := hμ_loc
  exact hP_cont x₀ r hr ((sphere_measure_eq_zero_iff_tendsto_variationalPerimeter_ball b μ
    zero_lt_one (fun U hU _ ↦ hμ_open U hU)).mp hsph)

/-- Global compactness for sequences of perimeter minimizers on `univ`. -/
theorem exists_subsequence_univ_isLocalPerimeterMinimizer
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (E_seq : ℕ → Set (Space d))
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E_seq j) univ) :
    ∃ (φ : ℕ → ℕ) (E : Set (Space d)),
      StrictMono φ ∧
      IsLocalPerimeterMinimizer b E univ ∧
      (∀ K : Set (Space d), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K,
          ‖(E_seq (φ j)).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) ∧
      (∀ x₀ : Space d, ∀ r : ℝ, 0 < r →
        Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
          (𝓝 (variationalPerimeter b E (ball x₀ r))) →
        Tendsto (fun j ↦ variationalPerimeter b (E_seq (φ j)) (ball x₀ r)) atTop
          (𝓝 (variationalPerimeter b E (ball x₀ r)))) ∧
      (∀ x₀ : Space d, ∀ r : ℝ, 0 < r →
        ∀ μ : Measure (Space d), IsLocallyFiniteMeasure μ →
          (∀ U, IsOpen U → μ U = variationalPerimeter b E U) →
          μ (sphere x₀ r) = 0 →
          Tendsto (fun j ↦ variationalPerimeter b (E_seq (φ j)) (ball x₀ r)) atTop
            (𝓝 (variationalPerimeter b E (ball x₀ r)))) :=
  exists_subsequence_univ_isLocalPerimeterMinimizer_of_eventually_ball hd b E_seq
    fun _ _ ↦ Eventually.of_forall fun j ↦ (hmin j).mono isOpen_ball (subset_univ _)

/-- Local BV compactness on `ball 0 R₀` (`0 < R₀`) for measurable sets with eventual perimeter
bounds on strictly smaller concentric balls. -/
theorem exists_subsequence_indicator_tendsto_ball_zero_of_eventually_perimeter_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (E_seq : ℕ → Set (Space d))
    (hbound : ∀ r : ℝ, 0 < r → r < R₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ j in atTop, MeasurableSet (E_seq j) ∧
        variationalPerimeter b (E_seq j) (ball 0 r) ≤ ENNReal.ofReal C) :
    ∃ (φ : ℕ → ℕ) (E : Set (Space d)), StrictMono φ ∧ MeasurableSet E ∧
      ∀ K : Set (Space d), IsCompact K → K ⊆ ball 0 R₀ →
        Tendsto (fun j ↦ ∫ x in K,
          ‖(E_seq (φ j)).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0) := by
  classical
  let A : ℕ → Set (Space d) := fun j ↦ if MeasurableSet (E_seq j) then E_seq j else ∅
  have hA_meas (j : ℕ) : MeasurableSet (A j) := by
    dsimp [A]
    split_ifs with h
    · exact h
    · exact MeasurableSet.empty
  obtain ⟨_, -, hA_ev₀⟩ := hbound (R₀ / 2) (half_pos hR₀) (half_lt_self hR₀)
  have hA_ev : ∀ᶠ j in atTop, A j = E_seq j := by
    filter_upwards [hA_ev₀] with j hj
    simp [A, hj.1]
  let r_fam : ℕ → ℝ := fun k ↦ (1 - 1 / ((k : ℝ) + 2)) * R₀
  have hr_fam_pos (k : ℕ) : 0 < r_fam k := by
    have h1 : 1 / ((k : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    exact mul_pos (sub_pos.mpr h1) hR₀
  have hr_fam_lt (k : ℕ) : r_fam k < R₀ := by
    have hpos : 0 < 1 / ((k : ℝ) + 2) := by positivity
    calc
      r_fam k < 1 * R₀ := mul_lt_mul_of_pos_right (by linarith) hR₀
      _ = R₀ := one_mul R₀
  have hr_fam_mono : Monotone r_fam := fun k l hkl ↦ by
    apply mul_le_mul_of_nonneg_right _ hR₀.le
    have hdiv : 1 / ((l : ℝ) + 2) ≤ 1 / ((k : ℝ) + 2) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hkl 2)
    linarith
  let R_mid : ℕ → ℝ := fun k ↦ (r_fam k + R₀) / 2
  have hR_mid_gt (k : ℕ) : r_fam k < R_mid k := by dsimp [R_mid]; linarith [hr_fam_lt k]
  have hR_mid_lt (k : ℕ) : R_mid k < R₀ := by dsimp [R_mid]; linarith [hr_fam_lt k]
  have hC_ex (k : ℕ) := hbound (R_mid k) ((hr_fam_pos k).trans (hR_mid_gt k)) (hR_mid_lt k)
  choose C hC hC_ev using hC_ex
  obtain ⟨φ, hφ, hlim⟩ := exists_simultaneous_mollified_phaseIndicator_subsequence A hA_meas r_fam
  let F : ℕ → Space d → ℝ := fun j ↦ (A (φ j)).indicator (fun _ ↦ (1 : ℝ))
  have hFi (j k : ℕ) : IntegrableOn (F j) (closedBall 0 (r_fam k)) volume :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 _)).indicator (hA_meas (φ j))
  have hc (k : ℕ) : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N,
      (∫ x in closedBall 0 (r_fam k), ‖F i x - F j x‖) < ε := by
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt (sub_pos.mpr (hR_mid_gt k))
    refine integral_cauchy_of_eventually_approximations F
      (fun n j ↦ mollify (F j) (n + n₀))
      (fun n ↦ (1 / (((n + n₀ : ℕ) : ℝ) + 1)) * C k)
      (fun j ↦ hFi j k)
      (fun n j ↦ (mollify_contDiff_of_locallyIntegrable
        (locallyIntegrable_phaseIndicator (hA_meas (φ j))) (n + n₀)).continuous.continuousOn
          |>.integrableOn_compact (isCompact_closedBall 0 _))
      (by
        have ht0 := (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat n₀))
          |>.mul_const (C k)
        simpa only [Function.comp_def, zero_mul] using ht0)
      (fun n ↦ ?_) (fun n ↦ ?_)
    · filter_upwards [hφ.tendsto_atTop.eventually (hC_ev k)] with j hj
      have hA_eq : A (φ j) = E_seq (φ j) := by simp [A, hj.1]
      have hle_n₀ : 1 / (((n + n₀ : ℕ) : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity)
          (by exact_mod_cast Nat.add_le_add_right (Nat.le_add_left n₀ n) 1)
      have hrR : r_fam k + 1 / (((n + n₀ : ℕ) : ℝ) + 1) < R_mid k := by linarith
      simp_rw [norm_sub_rev (F j _) (mollify (F j) (n + n₀) _)]
      refine integral_norm_mollify_phaseIndicator_sub_le b (hA_meas (φ j)) (n + n₀)
        hrR (hC k) ?_
      rw [hA_eq]
      exact hj.2
    · obtain ⟨v, hv⟩ := hlim (n + n₀) k
      exact integral_cauchy_of_uniform_convergence (isCompact_closedBall 0 (r_fam k))
        (fun j ↦ mollify (F j) (n + n₀))
        (fun j ↦ (mollify_contDiff_of_locallyIntegrable
          (locallyIntegrable_phaseIndicator (hA_meas (φ j))) (n + n₀)).continuous.continuousOn
            |>.integrableOn_compact (isCompact_closedBall 0 _)) v hv
  have hlocal (k : ℕ) : ∃ W : Space d → ℝ, IntegrableOn W (closedBall 0 (r_fam k)) volume ∧
      (∀ x, W x ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫ x in closedBall 0 (r_fam k), ‖F j x - W x‖) atTop (𝓝 0) := by
    obtain ⟨V₀, hV₀, hV₀_lim⟩ :=
      exists_integral_limit_of_cauchy (volume.restrict (closedBall 0 (r_fam k))) F
        (fun j ↦ hFi j k) (hc k)
    let W : Space d → ℝ := fun x ↦ max 0 (min 1 (V₀ x))
    have hW_Icc (x : Space d) : W x ∈ Icc (0 : ℝ) 1 :=
      ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    have hW_meas : AEStronglyMeasurable W (volume.restrict (closedBall 0 (r_fam k))) :=
      aestronglyMeasurable_const.sup (aestronglyMeasurable_const.inf hV₀.aestronglyMeasurable)
    let _ : IsFiniteMeasure (volume.restrict (closedBall (0 : Space d) (r_fam k))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall 0 _).measure_lt_top⟩
    have hW_int : IntegrableOn W (closedBall 0 (r_fam k)) volume :=
      Integrable.of_bound hW_meas 1 (Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hW_Icc x).1]; exact (hW_Icc x).2)
    have hW_lim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r_fam k), ‖F j x - W x‖) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hV₀_lim
        (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun j ↦ ?_
      refine integral_mono ((hFi j k).sub hW_int).norm ((hFi j k).sub hV₀).norm fun x ↦ ?_
      have hFx : F j x ∈ Icc (0 : ℝ) 1 := by
        by_cases hx : x ∈ A (φ j) <;> simp [F, hx]
      exact norm_sub_clamp_unit_le hFx
    exact ⟨W, hW_int, hW_Icc, hW_lim⟩
  choose W hW_int hW_Icc hW_lim using hlocal
  let S : ℕ → Set (Space d) := fun k ↦ closedBall (0 : Space d) (r_fam k) ∪ (ball 0 R₀)ᶜ
  let W_ext : ℕ → Space d → ℝ := fun k x ↦ if x ∈ ball (0 : Space d) R₀ then W k x else 0
  have hS_meas (k : ℕ) : MeasurableSet (S k) :=
    measurableSet_closedBall.union isOpen_ball.measurableSet.compl
  have hball_cover : ∀ x ∈ ball (0 : Space d) R₀, ∃ k : ℕ, x ∈ closedBall 0 (r_fam k) := by
    intro x hx
    have hx_lt : ‖x‖ < R₀ := by simpa [mem_ball, dist_zero_right] using hx
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos (sub_pos.mpr hx_lt) hR₀)
    refine ⟨k, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have hk' : 1 / ((k : ℝ) + 2) ≤ (R₀ - ‖x‖) / R₀ :=
      (div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)).trans hk.le
    have hmul := mul_le_mul_of_nonneg_right hk' hR₀.le
    rw [div_mul_cancel₀ _ hR₀.ne'] at hmul
    dsimp [r_fam]
    linarith
  have hS_cover (x : Space d) : ∃ k : ℕ, x ∈ S k := by
    by_cases hx : x ∈ ball (0 : Space d) R₀
    · obtain ⟨k, hk⟩ := hball_cover x hx
      exact ⟨k, Or.inl hk⟩
    · exact ⟨0, Or.inr hx⟩
  have hcompat_ext (k l : ℕ) (hkl : k ≤ l) :
      W_ext k =ᵐ[volume.restrict (S k)] W_ext l := by
    have hs : closedBall (0 : Space d) (r_fam k) ⊆ closedBall 0 (r_fam l) :=
      closedBall_subset_closedBall (hr_fam_mono hkl)
    have hW_kl : W k =ᵐ[volume.restrict (closedBall 0 (r_fam k))] W l :=
      ae_eq_of_integral_limits F (fun j ↦ hFi j k) (hW_int k) ((hW_int l).mono_set hs)
        (hW_lim k) (integral_limit_mono_set hs F (W l) (fun j ↦ hFi j l) (hW_int l) (hW_lim l))
    refine (ae_restrict_iff' (hS_meas k)).mpr ?_
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp hW_kl] with x hx hxS
    rcases hxS with hxk | hxcompl
    · have hxb : x ∈ ball (0 : Space d) R₀ :=
        (closedBall_subset_ball (hr_fam_lt k)) hxk
      simp only [W_ext, hxb, ↓reduceIte, hx hxk]
    · dsimp [W_ext]
      split_ifs with hxb
      · exact (hxcompl hxb).elim
      · rfl
  obtain ⟨v₀, hv₀⟩ := exists_ae_gluing volume S hS_meas hS_cover W_ext hcompat_ext
  let w : Space d → ℝ := fun x ↦ if x ∈ ball (0 : Space d) R₀ then max 0 (min 1 (v₀ x)) else 0
  have hw_Icc (x : Space d) : w x ∈ Icc (0 : ℝ) 1 := by
    dsimp [w]
    split_ifs
    · exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    · exact ⟨le_rfl, zero_le_one⟩
  have hw_eq (k : ℕ) : w =ᵐ[volume.restrict (closedBall 0 (r_fam k))] W k := by
    have hsub_S : closedBall (0 : Space d) (r_fam k) ⊆ S k := subset_union_left
    have hv₀_k : ∀ᵐ x ∂volume, x ∈ closedBall (0 : Space d) (r_fam k) → v₀ x = W_ext k x :=
      (ae_restrict_iff' measurableSet_closedBall).mp
        (ae_restrict_of_ae_restrict_of_subset hsub_S (hv₀ k))
    refine (ae_restrict_iff' measurableSet_closedBall).mpr ?_
    filter_upwards [hv₀_k] with x hx hxk
    have hxb : x ∈ ball (0 : Space d) R₀ := (closedBall_subset_ball (hr_fam_lt k)) hxk
    have h1 := hx hxk
    simp only [W_ext, hxb, ↓reduceIte] at h1
    simp only [w, hxb, ↓reduceIte, h1, min_eq_right (hW_Icc k x).2, max_eq_right (hW_Icc k x).1]
  have hw_int (k : ℕ) : IntegrableOn w (closedBall 0 (r_fam k)) volume :=
    (hW_int k).congr (hw_eq k).symm
  have hw_lim (k : ℕ) :
      Tendsto (fun j ↦ ∫ x in closedBall 0 (r_fam k), ‖F j x - w x‖) atTop (𝓝 0) := by
    refine (hW_lim k).congr' (Eventually.of_forall fun j ↦ ?_)
    refine integral_congr_ae ?_
    filter_upwards [hw_eq k] with x hx
    rw [hx]
  let T_cov : ℕ → Set (Space d) := fun n ↦
    match n with
    | 0 => (ball (0 : Space d) R₀)ᶜ
    | k + 1 => closedBall (0 : Space d) (r_fam k)
  have hT_iUnion : (⋃ n : ℕ, T_cov n) = univ := by
    refine eq_univ_of_forall fun x ↦ mem_iUnion.mpr ?_
    by_cases hx : x ∈ ball (0 : Space d) R₀
    · obtain ⟨k, hk⟩ := hball_cover x hx
      exact ⟨k + 1, hk⟩
    · exact ⟨0, hx⟩
  have hw_meas : AEStronglyMeasurable w volume := by
    have hloc_meas (n : ℕ) : AEStronglyMeasurable w (volume.restrict (T_cov n)) := by
      cases n with
      | zero =>
        refine (aestronglyMeasurable_const (b := (0 : ℝ))).congr ?_
        refine (ae_restrict_iff' isOpen_ball.measurableSet.compl).mpr ?_
        refine Eventually.of_forall fun x hx ↦ ?_
        dsimp [w]
        split_ifs with hxb
        · exact (hx hxb).elim
        · rfl
      | succ k => exact (hw_int k).aestronglyMeasurable
    simpa only [hT_iUnion, Measure.restrict_univ] using AEStronglyMeasurable.iUnion hloc_meas
  have hw_two : ∀ᵐ x ∂volume, w x = 0 ∨ w x = 1 := by
    have hloc_two (n : ℕ) : ∀ᵐ x ∂volume.restrict (T_cov n), w x = 0 ∨ w x = 1 := by
      cases n with
      | zero =>
        refine (ae_restrict_iff' isOpen_ball.measurableSet.compl).mpr ?_
        refine Eventually.of_forall fun x hx ↦ Or.inl ?_
        dsimp [w]
        split_ifs with hxb
        · exact (hx hxb).elim
        · rfl
      | succ k =>
        exact ae_eq_zero_or_one_of_indicator_integral_limit (fun j ↦ hA_meas (φ j))
          (isCompact_closedBall 0 (r_fam k)) (hw_int k).aestronglyMeasurable hw_Icc (hw_lim k)
    have hall := (ae_restrict_iUnion_iff T_cov (fun x ↦ w x = 0 ∨ w x = 1)).mpr hloc_two
    simpa only [hT_iUnion, Measure.restrict_univ] using hall
  obtain ⟨E, hE, hwE⟩ := exists_measurable_indicator_of_two_values hw_meas 1 hw_two
  refine ⟨φ, E, hφ, hE, fun K hK hKsub ↦ ?_⟩
  obtain ⟨r₁, r₂, _, hr₁₂, hr₂R₀, hKr₁⟩ := exists_radii_lt_subset_ball_of_isCompact hR₀ hK hKsub
  have hr₁R₀ : r₁ < R₀ := hr₁₂.trans hr₂R₀
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos (sub_pos.mpr hr₁R₀) hR₀)
  have hr₁_le : r₁ ≤ r_fam k := by
    have hk' : 1 / ((k : ℝ) + 2) ≤ (R₀ - r₁) / R₀ :=
      (div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)).trans hk.le
    have hmul := mul_le_mul_of_nonneg_right hk' hR₀.le
    rw [div_mul_cancel₀ _ hR₀.ne'] at hmul
    dsimp [r_fam]
    linarith
  have hs : K ⊆ closedBall 0 (r_fam k) :=
    hKr₁.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall hr₁_le))
  have hFK : Tendsto (fun j ↦ ∫ x in K, ‖F j x - w x‖) atTop (𝓝 0) :=
    integral_limit_mono_set hs F w (fun j ↦ hFi j k) (hw_int k) (hw_lim k)
  refine hFK.congr' ?_
  filter_upwards [hφ.tendsto_atTop.eventually hA_ev] with j hj
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hwE] with x hx
  dsimp [F]
  rw [hj, hx]

/-- Local compactness on `ball c₀ R₀` (`0 < R₀`) for families that are eventually local perimeter
minimizers on every strictly smaller concentric ball `ball c₀ r` (`0 < r < R₀`). -/
theorem exists_subsequence_ball_isLocalPerimeterMinimizer_of_eventually_ball
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {c₀ : Space d} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (E_seq : ℕ → Set (Space d))
    (hmin : ∀ r : ℝ, 0 < r → r < R₀ →
      ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (E_seq j) (ball c₀ r)) :
    ∃ (φ : ℕ → ℕ) (E : Set (Space d)),
      StrictMono φ ∧
      IsLocalPerimeterMinimizer b E (ball c₀ R₀) ∧
      (∀ K : Set (Space d), IsCompact K → K ⊆ ball c₀ R₀ →
        Tendsto (fun j ↦ ∫ x in K,
          ‖(E_seq (φ j)).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) ∧
      (∀ x₀ : Space d, ∀ r : ℝ, 0 < r → closedBall x₀ r ⊆ ball c₀ R₀ →
        Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
          (𝓝 (variationalPerimeter b E (ball x₀ r))) →
        Tendsto (fun j ↦ variationalPerimeter b (E_seq (φ j)) (ball x₀ r)) atTop
          (𝓝 (variationalPerimeter b E (ball x₀ r)))) := by
  let T : Space d → Space d := fun y ↦ c₀ + (1 : ℝ) • y
  let S_inv : Space d → Space d := fun x ↦ -c₀ + x
  have hT_ball (r : ℝ) : T ⁻¹' ball c₀ r = ball 0 r := by
    ext y
    simp [T, mem_ball, dist_eq_norm]
  have hmin₀ (r : ℝ) (hr : 0 < r) (hrR₀ : r < R₀) :
      ∀ᶠ j in atTop, IsLocalPerimeterMinimizer b (T ⁻¹' E_seq j) (ball 0 r) := by
    filter_upwards [hmin r hr hrR₀] with j hj
    have hp := hj.preimage_add_smul hd c₀ zero_lt_one
    rwa [hT_ball r] at hp
  have hbound₀ (r : ℝ) (hr : 0 < r) (hrR₀ : r < R₀) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j in atTop, MeasurableSet (T ⁻¹' E_seq j) ∧
        variationalPerimeter b (T ⁻¹' E_seq j) (ball 0 r) ≤ ENNReal.ofReal C := by
    let r' : ℝ := (r + R₀) / 2
    let C : ℝ :=
      ballGluingConstant * (d : ℝ) * volume.real (ball (0 : Space d) 1) * r ^ (d - 1)
    refine ⟨C, mul_nonneg
      (mul_nonneg (mul_nonneg ballGluingConstant_pos.le (Nat.cast_nonneg d)) measureReal_nonneg)
      (pow_nonneg hr.le _), ?_⟩
    filter_upwards [hmin₀ r' (by dsimp [r']; linarith) (by dsimp [r']; linarith)] with j hj
    exact ⟨hj.measurableSet, hj.perimeter_ball_le hd hr
      (closedBall_subset_ball (by dsimp [r']; linarith))⟩
  obtain ⟨φ, E₀, hφ, hE₀, ht₀⟩ :=
    exists_subsequence_indicator_tendsto_ball_zero_of_eventually_perimeter_bound
      b hR₀ (fun j ↦ T ⁻¹' E_seq j) hbound₀
  let E : Set (Space d) := S_inv ⁻¹' E₀
  have hE_meas : MeasurableSet E := hE₀.preimage (continuous_const.add continuous_id).measurable
  have hTE : T ⁻¹' E = E₀ := by
    ext y
    simp [T, S_inv, E]
  have ht (K : Set (Space d)) (hK : IsCompact K) (hKsub : K ⊆ ball c₀ R₀) :
      Tendsto (fun j ↦ ∫ x in K,
        ‖(E_seq (φ j)).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0) := by
    let K₀ : Set (Space d) := S_inv '' K
    have hK₀_comp : IsCompact K₀ := hK.image (continuous_const.add continuous_id)
    have hK₀_sub : K₀ ⊆ ball 0 R₀ := by
      rintro _ ⟨x, hx, rfl⟩
      have hxb : dist x c₀ < R₀ := mem_ball.mp (hKsub hx)
      rw [mem_ball, dist_zero_right]
      simpa [S_inv, dist_eq_norm, sub_eq_add_neg, add_comm] using hxb
    have hK_pre : S_inv ⁻¹' K₀ = K := by
      ext x
      simp only [K₀, mem_preimage, mem_image, S_inv]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hxy : y = x := by
          have := congrArg (c₀ + ·) hyx
          simpa using this
        rwa [← hxy]
      · exact fun hx ↦ ⟨x, hx, rfl⟩
    refine (ht₀ K₀ hK₀_comp hK₀_sub).congr fun j ↦ ?_
    have hmp := measurePreserving_add_left volume (-c₀)
    have hchg := hmp.setIntegral_preimage_emb
      (MeasurableEquiv.addLeft (-c₀)).measurableEmbedding
      (fun y ↦ ‖(T ⁻¹' E_seq (φ j)).indicator (fun _ ↦ (1 : ℝ)) y -
        E₀.indicator (fun _ ↦ (1 : ℝ)) y‖) K₀
    rw [show (fun x ↦ -c₀ + x) = S_inv from rfl, hK_pre] at hchg
    refine hchg.symm.trans (setIntegral_congr_fun hK.measurableSet fun x _ ↦ ?_)
    have hTS (z : Space d) : T (S_inv z) = z := by simp [T, S_inv]
    have h1 : (T ⁻¹' E_seq (φ j)).indicator (fun _ ↦ (1 : ℝ)) (S_inv x) =
        (E_seq (φ j)).indicator (fun _ ↦ (1 : ℝ)) x := by
      by_cases hxE : x ∈ E_seq (φ j)
      · have hm : S_inv x ∈ T ⁻¹' E_seq (φ j) := by simpa [hTS x] using hxE
        simp [hxE, hm]
      · have hm : S_inv x ∉ T ⁻¹' E_seq (φ j) := by simpa [hTS x] using hxE
        simp [hxE, hm]
    have h2 : E₀.indicator (fun _ ↦ (1 : ℝ)) (S_inv x) =
        E.indicator (fun _ ↦ (1 : ℝ)) x := by
      have hxE₀ : S_inv x ∈ E₀ ↔ x ∈ E := Iff.rfl
      by_cases hxE : x ∈ E <;> simp [hxE, hxE₀]
    rw [h1, h2]
  have hE_lt (r : ℝ) (hr : 0 < r) (hrR₀ : r < R₀) :
      IsLocalPerimeterMinimizer b E (ball c₀ r) :=
    isLocalPerimeterMinimizer_ball_of_eventually_tendsto_indicator hd b hr
      (hφ.tendsto_atTop.eventually (hmin r hr hrR₀)) hE_meas
      fun K hK hKr ↦ ht K hK (hKr.trans (ball_subset_ball hrR₀.le))
  have hE_min : IsLocalPerimeterMinimizer b E (ball c₀ R₀) :=
    isLocalPerimeterMinimizer_ball_of_lt hR₀ hE_lt
  refine ⟨φ, E, hφ, hE_min, ht, fun x₀ r hr hsub hcont ↦ ?_⟩
  obtain ⟨r₁, r₂, hr₁, hr₁₂, hr₂R₀, hsub₁⟩ :=
    exists_radii_lt_subset_ball_of_isCompact hR₀ (isCompact_closedBall x₀ r) hsub
  have hr₁R₀ : r₁ < R₀ := hr₁₂.trans hr₂R₀
  exact tendsto_variationalPerimeter_ball_of_eventually_right_continuous hd b
    (hφ.tendsto_atTop.eventually (hmin r₁ hr₁ hr₁R₀)) hE_meas
    (fun K hK hKr₁ ↦ ht K hK (hKr₁.trans (ball_subset_ball hr₁R₀.le))) hr hsub₁ hcont

/-- Local compactness on `ball c₀ R₀` (`0 < R₀`) for sequences of local perimeter minimizers. -/
theorem exists_subsequence_ball_isLocalPerimeterMinimizer
    {d : ℕ} (hd : 1 ≤ d) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {c₀ : Space d} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (E_seq : ℕ → Set (Space d))
    (hmin : ∀ j, IsLocalPerimeterMinimizer b (E_seq j) (ball c₀ R₀)) :
    ∃ (φ : ℕ → ℕ) (E : Set (Space d)),
      StrictMono φ ∧
      IsLocalPerimeterMinimizer b E (ball c₀ R₀) ∧
      (∀ K : Set (Space d), IsCompact K → K ⊆ ball c₀ R₀ →
        Tendsto (fun j ↦ ∫ x in K,
          ‖(E_seq (φ j)).indicator (fun _ ↦ (1 : ℝ)) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) ∧
      (∀ x₀ : Space d, ∀ r : ℝ, 0 < r → closedBall x₀ r ⊆ ball c₀ R₀ →
        Tendsto (fun s ↦ variationalPerimeter b E (ball x₀ s)) (𝓝[>] r)
          (𝓝 (variationalPerimeter b E (ball x₀ r))) →
        Tendsto (fun j ↦ variationalPerimeter b (E_seq (φ j)) (ball x₀ r)) atTop
          (𝓝 (variationalPerimeter b E (ball x₀ r)))) :=
  exists_subsequence_ball_isLocalPerimeterMinimizer_of_eventually_ball hd b hR₀ E_seq
    fun _ _ hrR₀ ↦ Eventually.of_forall fun j ↦
      (hmin j).mono isOpen_ball (ball_subset_ball hrR₀.le)

end SerrinEpigraph
