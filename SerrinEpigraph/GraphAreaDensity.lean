module

public import SerrinEpigraph.LocalRecoveryBound

/-!
# Local oscillation control of graph area density
-/

public section

open Set Metric MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- The Euclidean area density of a graph over its horizontal base. -/
@[expose] noncomputable def graphAreaDensity {d : ℕ} (b : Space d → ℝ) (y : Space d) : ℝ :=
  Real.sqrt (1 + ‖gradient b y‖ ^ 2)

theorem graphAreaDensity_pos {d : ℕ} (b : Space d → ℝ) (y : Space d) :
    0 < graphAreaDensity b y := Real.sqrt_pos.mpr (by positivity)

theorem graphAreaDensity_sq {d : ℕ} (b : Space d → ℝ) (y : Space d) :
    graphAreaDensity b y ^ 2 = 1 + ‖gradient b y‖ ^ 2 := Real.sq_sqrt (by positivity)

/-- A C1 graph has continuous area density. -/
theorem continuous_graphAreaDensity {d : ℕ} {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) :
    Continuous (graphAreaDensity b) := by
  have hc := (hb.continuous_fderiv (by norm_num)).norm
  change Continuous (fun y ↦ Real.sqrt (1 + ‖gradient b y‖ ^ 2))
  simp_rw [norm_gradient_eq_norm_fderiv]
  exact (continuous_const.add (hc.pow 2)).sqrt

/-- Near every point, one constant bounds the slope and exceeds the area density by at most ε. -/
theorem exists_local_graphAreaDensity_bound {d : ℕ} {b : Space d → ℝ}
    (hb : ContDiff ℝ 1 b) (y : Space d) {ε : ℝ} (hε : 0 < ε) :
    ∃ r L : ℝ, 0 < r ∧ 0 < L ∧ ∀ z ∈ ball y r,
      1 + ‖gradient b z‖ ^ 2 ≤ L ^ 2 ∧ L ≤ graphAreaDensity b z + ε := by
  obtain ⟨r, hr, hosc⟩ := Metric.continuousAt_iff.mp
    (continuous_graphAreaDensity hb).continuousAt (ε / 2) (by positivity)
  have hy := graphAreaDensity_pos b y
  refine ⟨r, graphAreaDensity b y + ε / 2, hr, by positivity, ?_⟩
  intro z hz
  have he := hosc hz
  rw [Real.dist_eq] at he
  have he' := abs_lt.mp he
  constructor
  · have hzpos := (graphAreaDensity_pos b z).le
    have hypos := (graphAreaDensity_pos b y).le
    rw [← graphAreaDensity_sq b z]
    nlinarith
  · linarith

/-- A nearly constant upper density gives an area-integral bound with an explicit volume error. -/
theorem graphAreaDensity_integral_upper {d : ℕ} {b : Space d → ℝ}
    (hb : ContDiff ℝ 1 b) {A : Set (Space d)} (hA : IsCompact A) {L ε : ℝ}
    (hbound : ∀ y ∈ A, L ≤ graphAreaDensity b y + ε) :
    L * (volume A).toReal ≤ (∫ y in A, graphAreaDensity b y) + ε * (volume A).toReal := by
  have hi := (continuous_graphAreaDensity hb).continuousOn.integrableOn_compact (μ := volume) hA
  have hc : IntegrableOn (fun _ : Space d ↦ L) A :=
    continuous_const.continuousOn.integrableOn_compact hA
  have hεi : IntegrableOn (fun _ : Space d ↦ ε) A :=
    continuous_const.continuousOn.integrableOn_compact hA
  have he := setIntegral_mono_on hc (hi.add hεi) hA.measurableSet hbound
  simpa only [Pi.add_apply, integral_add hi hεi, integral_const, smul_eq_mul,
    measureReal_def, Measure.restrict_apply_univ, mul_comm] using he

/-- On a sufficiently small graph patch, recovery energy is bounded by graph area plus
an arbitrarily small base-volume error, times the exact transition action. -/
theorem RigidityHypotheses.exists_local_graphRecovery_area_bound
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) (y : Space d) {ε : ℝ} (hε : 0 < ε) :
    ∃ r L : ℝ, 0 < r ∧ 0 < L ∧ ∀ (δ R : ℝ), 0 < δ → 0 < R →
      ∀ (A : Set (Space d)), IsCompact A → A ⊆ ball y r →
      ∀ (K : Set (Space (d + 1))), IsCompact K → (∀ x ∈ K, horizontal x ∈ A) →
      (∫ x in K, rescaledPhaseEnergyDensity f R
        (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L)) x) ≤
        ((∫ z in A, graphAreaDensity b z) + ε * (volume A).toReal) *
          recoveryActionPrimitive f δ 1 := by
  obtain ⟨r, L, hrpos, hL, hloc⟩ := exists_local_graphAreaDensity_bound hb y hε
  refine ⟨r, L, hrpos, hL, ?_⟩
  intro δ R hδ hR A hA hsub K hK hproj
  have he := hr.graphRecovery_local_integral_energy_le h hδ hR hb hL hA.measurableSet
    hA.measure_ne_top hK hproj (fun x hx ↦ (hloc _ (hsub (hproj x hx))).1)
  have harea := graphAreaDensity_integral_upper hb hA (fun z hz ↦ (hloc z (hsub hz)).2)
  have hact : 0 ≤ recoveryActionPrimitive f δ 1 := by
    rw [← hr.integral_recoveryLayerDensity h hδ hR]
    exact integral_nonneg (hr.recoveryLayerDensity_nonneg h hδ hR.le)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ hact
  simpa only [mul_comm] using harea

end SerrinEpigraph
