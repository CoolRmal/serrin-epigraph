module

public import SerrinEpigraph.LocalizedGraphSubsequence
public import SerrinEpigraph.RecoveryMinimality
public import SerrinEpigraph.LimitingGraphComparison

/-!
# Localized perimeter comparison for graph competitors
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- The fixed limiting phase has interior perimeter bounded by a C1 graph
competitor's perimeter in any open neighborhood of the comparison ball.
Only annular phase agreement is assumed; cutoffs, partitions, and compatible
recovery scales are constructed inside the proof. -/
theorem RigidityHypotheses.limiting_perimeter_le_graph_competitor_perimeter
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {r t a : ℝ} (hradius : 0 < r) (ht : 0 < t) (har : a < r)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t),
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    {b : Space m → ℝ} (hb : ContDiff ℝ 1 b)
    (hagree : ∀ x ∈ closedBall 0 (r + t) \ ball 0 r, x ∈ E ↔ x ∈ epigraph b)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω) (hKΩ : closedBall 0 (r + t) ⊆ Ω) :
    variationalPerimeter basis E (ball 0 a) ≤ variationalPerimeter basis (epigraph b) Ω := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_closedBall 0 (r + t)) hΩ hKΩ
  obtain ⟨χ, hχsmooth, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) hVo isClosed_closedBall hKV
  have hχc : HasCompactSupport χ := by
    change IsCompact (closure (Function.support χ))
    rwa [hχsupport]
  obtain ⟨M, hχ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχc hχsmooth one_ne_zero
  have hχval (x : Space (m + 1)) : χ x ∈ Icc (0 : ℝ) 1 := hχrange ⟨x, rfl⟩
  have hχs : tsupport χ ⊆ Ω := by
    change closure (Function.support χ) ⊆ Ω
    rwa [hχsupport]
  let D := horizontal '' closedBall (0 : Space (m + 1)) (r + t)
  have hD : IsCompact D := (isCompact_closedBall 0 (r + t)).image continuous_horizontal
  obtain ⟨V₀, hV₀o, hDV, _, hV₀c⟩ :=
    exists_open_between_and_isCompact_closure hD isOpen_univ (subset_univ D)
  have hDA : D ⊆ interior (closure V₀) := hDV.trans hV₀o.subset_interior_closure
  obtain ⟨n, B, v, _, hnt, _, hRnt, hv, hval, hvlim, hbound, hBt⟩ :=
    hr.exists_localized_graphRecovery_subsequence h R
      (fun j ↦ zero_lt_one.trans_le (hR j)) hRt hb hV₀c hD hDA hχ
      (fun x ↦ (hχval x).1) (isCompact_closedBall 0 (r + t))
      (fun x hx ↦ ⟨x, hx, rfl⟩) (fun x hx ↦ ((hχone x).mp hx).ge)
  have he := hr.perimeter_le_recovery_bound_of_annular_agreement h basis hradius ht har
    (fun j ↦ hR (n j)) hRnt hv hval hE (isOpen_epigraph hb.continuous).measurableSet
    hagree (hUlim.comp hnt) hvlim hbound hBt
  have hc : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  rw [mul_comm (∫ y in closure V₀, χ (point y (b y)) * graphAreaDensity b y),
    ENNReal.ofReal_mul hc.le] at he
  have hp := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hc).ne'
    ENNReal.ofReal_ne_top).mp he
  apply hp.trans
  apply le_trans _ (weighted_graph_area_le_perimeter basis hb hχ.continuous hχc hχval hχs)
  apply ENNReal.ofReal_le_ofReal
  have htrace : Continuous (fun y ↦ χ (point y (b y))) := hχ.continuous.comp
    (pointContinuousLinearMap.continuous.comp (continuous_id.prodMk hb.continuous))
  have hct : HasCompactSupport (fun y ↦ χ (point y (b y))) := by
    simpa only [add_zero] using hasCompactSupport_graph_section (b := b) hχc 0
  exact setIntegral_le_integral
    ((htrace.mul (continuous_graphAreaDensity hb)).integrable_of_hasCompactSupport hct.mul_right)
    (Eventually.of_forall (fun y ↦ mul_nonneg (hχval _).1 (graphAreaDensity_pos b y).le))

/-- A fixed phase limit minimizes perimeter in a ball against every C1 graph
epigraph that agrees with it outside a strictly smaller concentric closed ball. -/
theorem RigidityHypotheses.limiting_phase_graph_minimality
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {s r₀ : ℝ} (hs : 0 < s) (hr₀ : r₀ < s)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    {b : Space m → ℝ} (hb : ContDiff ℝ 1 b)
    (hagree : ∀ x ∈ ball 0 s \ closedBall 0 r₀, x ∈ E ↔ x ∈ epigraph b) :
    variationalPerimeter basis E (ball 0 s) ≤
      variationalPerimeter basis (epigraph b) (ball 0 s) := by
  unfold variationalPerimeter at ⊢
  refine iSup_le (fun F ↦ iSup_le (fun hF ↦ iSup_le (fun hc ↦
    iSup_le (fun hFs ↦ iSup_le (fun hunit ↦ ?_)))))
  obtain ⟨a, has, hFa⟩ := exists_lt_subset_ball (isClosed_tsupport F) hFs
  obtain ⟨r, hlow, hrs⟩ := exists_between (max_lt has (max_lt hs hr₀))
  have har : a < r := (le_max_left _ _).trans_lt hlow
  have hrpos : 0 < r := (le_max_left 0 r₀).trans (le_max_right a (max 0 r₀)) |>.trans_lt hlow
  have hr₀r : r₀ < r := (le_max_right 0 r₀).trans (le_max_right a (max 0 r₀)) |>.trans_lt hlow
  let t := (s - r) / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hrts : r + t < s := by dsimp [t]; linarith
  have hsmall : closedBall (0 : Space (m + 1)) (r + t) ⊆ ball 0 s :=
    closedBall_subset_ball hrts
  have hiE : IntegrableOn (E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ)))
      (closedBall 0 s) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _)).indicator hE
  have hlim := integral_norm_sub_tendsto_of_subset (hsmall.trans ball_subset_closedBall)
    (fun j ↦ (((h.zeroExtension_continuous.comp
      (continuous_id.const_smul (R j))).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).sub hiE).norm) hUlim
  have hcomp := hr.limiting_perimeter_le_graph_competitor_perimeter h basis hrpos ht har
    hR hRt hE hlim hb (fun x hx ↦ hagree x ⟨hsmall hx.1, fun hx₀ ↦ hx.2
      (closedBall_subset_ball hr₀r hx₀)⟩) isOpen_ball hsmall
  apply le_trans _ hcomp
  unfold variationalPerimeter
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hc
    (le_iSup_of_le hFa (le_iSup_of_le hunit le_rfl))))

/-- The original PDE assumptions produce a single phase limit with local L1
convergence and perimeter minimality against compact graph perturbations in every ball. -/
theorem RigidityHypotheses.exists_limiting_phase_with_graph_minimality
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R (φ j) • x) -
          E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) ∧
      ∀ (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
        (s r₀ : ℝ), 0 < s → r₀ < s →
        ∀ b : Space m → ℝ, ContDiff ℝ 1 b →
        (∀ x ∈ ball 0 s \ closedBall 0 r₀, x ∈ E ↔ x ∈ epigraph b) →
        variationalPerimeter basis E (ball 0 s) ≤
          variationalPerimeter basis (epigraph b) (ball 0 s) := by
  obtain ⟨φ, hφ, E, hE, hlocal, _⟩ := hr.exists_limiting_phase_with_graph_comparison h R hR hRt
  refine ⟨φ, hφ, E, hE, hlocal, ?_⟩
  intro basis s r₀ hs hr₀ b hb hagree
  exact hr.limiting_phase_graph_minimality h basis hs hr₀
    (fun j ↦ hR (φ j)) (hRt.comp hφ.tendsto_atTop) hE
    (hlocal _ (isCompact_closedBall _ _)) hb hagree

end SerrinEpigraph
