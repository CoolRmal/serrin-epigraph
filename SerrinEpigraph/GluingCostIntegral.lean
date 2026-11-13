module

public import SerrinEpigraph.GluingCostBound
public import SerrinEpigraph.SelectedTransitionCutoff

/-!
# Integrability and integral formula for the gluing majorant
-/

public section

open Set MeasureTheory

namespace SerrinEpigraph

/-- The transition cost with an a priori cutoff gradient bound. -/
@[expose] noncomputable def gluingCost {d : ℕ} (f : ℝ → ℝ) (R G : ℝ)
    (U v : Space d → ℝ) (x : Space d) : ℝ :=
  max 2 (normalizedPotential f 0 / normalizedPotential f (1 / 2)) *
    (rescaledPhaseEnergyDensity f R U x + rescaledPhaseEnergyDensity f R v x) +
  (G ^ 2 / R + 4 * R * normalizedPotential f 0) * (v x - U x) ^ 2

/-- The rescaled energy of a normalized locally Lipschitz function is locally integrable. -/
theorem Hypotheses.integrableOn_rescaledPhaseEnergy
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {v : Space d → ℝ} (hv : LocallyLipschitz v)
    (hval : ∀ x, v x ∈ Icc (0 : ℝ) 1) (R : ℝ)
    {K : Set (Space d)} (hK : IsCompact K) :
    IntegrableOn (rescaledPhaseEnergyDensity f R v) K := by
  have hW : Continuous (fun x ↦ normalizedPotential f (v x)) :=
    h.normalizedPotential_continuousOn.comp_continuous hv.continuous hval
  have hi := ((integrableOn_gradient_sq_of_locallyLipschitz hv hK).div_const (2 * R)).add
    ((hW.continuousOn.integrableOn_compact hK).const_mul R)
  exact hi.indicator (isOpen_lt continuous_const hv.continuous).measurableSet

/-- The gluing cost is integrable on every compact set. -/
theorem Hypotheses.integrableOn_gluingCost
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {U v : Space d → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v)
    (hUval : ∀ x, U x ∈ Icc (0 : ℝ) 1) (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (R G : ℝ) {K : Set (Space d)} (hK : IsCompact K) :
    IntegrableOn (gluingCost f R G U v) K := by
  have hi := ((h.integrableOn_rescaledPhaseEnergy hU hUval R hK).add
    (h.integrableOn_rescaledPhaseEnergy hv hvval R hK)).const_mul
      (max 2 (normalizedPotential f 0 / normalizedPotential f (1 / 2)))
  have hig := ((hv.continuous.sub hU.continuous).pow 2).continuousOn.integrableOn_compact
    (μ := volume) hK
  exact hi.add (hig.const_mul (G ^ 2 / R + 4 * R * normalizedPotential f 0))

/-- The majorant is nonnegative for normalized input functions and nonnegative scale. -/
theorem RigidityHypotheses.gluingCost_nonneg
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {U v : Space d → ℝ}
    (hUval : ∀ x, U x ∈ Icc (0 : ℝ) 1) (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    {R : ℝ} (hR : 0 ≤ R) (G : ℝ) (x : Space d) : 0 ≤ gluingCost f R G U v x := by
  have hEU := hr.rescaledPhaseEnergyDensity_nonneg h hR hUval x
  have hEv := hr.rescaledPhaseEnergyDensity_nonneg h hR hvval x
  have hW := hr.normalizedPotential_nonneg h (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  unfold gluingCost
  positivity

/-- The integral of the majorant separates into the two energies and squared mismatch. -/
theorem Hypotheses.integral_gluingCost
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {U v : Space d → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v)
    (hUval : ∀ x, U x ∈ Icc (0 : ℝ) 1) (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (R G : ℝ) {K : Set (Space d)} (hK : IsCompact K) :
    (∫ x in K, gluingCost f R G U v x) =
      max 2 (normalizedPotential f 0 / normalizedPotential f (1 / 2)) *
        ((∫ x in K, rescaledPhaseEnergyDensity f R U x) +
          ∫ x in K, rescaledPhaseEnergyDensity f R v x) +
      (G ^ 2 / R + 4 * R * normalizedPotential f 0) * ∫ x in K, (v x - U x) ^ 2 := by
  have hiU := h.integrableOn_rescaledPhaseEnergy hU hUval R hK
  have hiv := h.integrableOn_rescaledPhaseEnergy hv hvval R hK
  have hig := ((hv.continuous.sub hU.continuous).pow 2).continuousOn.integrableOn_compact
    (μ := volume) hK
  have his := hiU.add hiv
  change IntegrableOn (fun x ↦ (v x - U x) ^ 2) K at hig
  change IntegrableOn (fun x ↦ rescaledPhaseEnergyDensity f R U x +
    rescaledPhaseEnergyDensity f R v x) K at his
  unfold gluingCost
  rw [integral_add (his.const_mul _) (hig.const_mul _),
    integral_const_mul, integral_const_mul, integral_add hiU hiv]

/-- The cutoff can be selected using the actual energy-and-mismatch majorant. -/
theorem RigidityHypotheses.exists_cutoff_with_small_gluing_cost
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ) (r t R : ℝ),
      0 < N → 0 < r → 0 < t → 0 ≤ R →
      ∀ U v : Space d → ℝ, LocallyLipschitz U → LocallyLipschitz v →
      (∀ x, U x ∈ Icc (0 : ℝ) 1) → (∀ x, v x ∈ Icc (0 : ℝ) 1) →
      ∃ η : Space d → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧
        tsupport η ⊆ Metric.ball 0 (r + t) ∧
        (∀ x ∈ Metric.ball 0 r, η x = 1) ∧
        (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, ‖gradient η x‖ ≤ C * N / t) ∧
        (∫ x in {x | 0 < η x ∧ η x < 1}, gluingCost f R (C * N / t) U v x) ≤
          (∫ x in Metric.closedBall 0 (r + t), gluingCost f R (C * N / t) U v x) / N := by
  obtain ⟨C, hC, hc⟩ := exists_cutoff_in_fixed_annulus_with_small_cost
  refine ⟨C, hC, fun d N r t R hN hradius ht hR U v hU hv hUval hvval ↦ ?_⟩
  exact hc d N r t hN hradius ht (gluingCost f R (C * N / t) U v)
    (h.integrableOn_gluingCost hU hv hUval hvval R _ (isCompact_closedBall _ _))
    (fun x _ ↦ hr.gluingCost_nonneg h hUval hvval hR _ x)

end SerrinEpigraph
