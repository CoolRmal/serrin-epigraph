module

public import SerrinEpigraph.RecoveryEnergyLocalization
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Recovery competitors from distance to the complement
-/

public section

open Set Metric MeasureTheory Filter
open scoped Topology NNReal

namespace SerrinEpigraph

/-- The recovery competitor of a set, using distance to its complement. -/
@[expose] noncomputable def distanceRecovery {d : ℕ} (f : ℝ → ℝ) (δ R : ℝ)
    (E : Set (Space d)) : Space d → ℝ :=
  geometricRecoveryProfile f δ R (fun x ↦ infDist x Eᶜ)

/-- For a proper open set, distance to its complement is positive precisely in the set. -/
theorem positive_infDist_compl_eq {d : ℕ} {E : Set (Space d)}
    (hE : IsOpen E) (hne : Eᶜ.Nonempty) : {x | 0 < infDist x Eᶜ} = E := by
  ext x
  simpa only [mem_ofPred_eq, mem_compl_iff, not_not] using
    (hE.isClosed_compl.notMem_iff_infDist_pos hne).symm

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ} {E : Set (Space d)}

/-- The distance competitor is globally Lipschitz with explicit transition-speed control. -/
theorem RigidityHypotheses.distanceRecovery_lipschitz
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    LipschitzWith
      (⟨Real.sqrt (2 * (normalizedPotential f 0 + δ)), Real.sqrt_nonneg _⟩ * ‖R‖₊)
      (distanceRecovery f δ R E) := by
  simpa only [distanceRecovery, mul_one] using
    hr.geometricRecoveryProfile_lipschitz h hδ (R := R) (lipschitz_infDist_pt Eᶜ)

/-- Distance competitors vanish on the complement, including the boundary of an open set. -/
theorem RigidityHypotheses.distanceRecovery_eq_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {x : Space d} (hx : x ∉ E) : distanceRecovery f δ R E x = 0 := by
  apply hr.recoveryProfile_eq_zero h hδ
  simp [infDist_zero_of_mem (show x ∈ Eᶜ from hx)]

/-- The distance construction converges locally in L1 to the given proper open set. -/
theorem RigidityHypotheses.distanceRecovery_integral_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hE : IsOpen E) (hne : Eᶜ.Nonempty)
    {δ R : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hR : ∀ j, 0 < R j)
    (hwidth : Tendsto (fun j ↦ recoveryTravelTime f (δ j) 1 / R j) atTop (𝓝 0))
    {K : Set (Space d)} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖distanceRecovery f (δ j) (R j) E x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
      atTop (𝓝 0) := by
  simpa only [distanceRecovery, positive_infDist_compl_eq hE hne] using
    hr.geometricRecoveryProfile_integral_limit h hδ hR hwidth
      (lipschitz_infDist_pt Eᶜ).continuous hK

/-- The distance competitor's energy is bounded by an integral over its interior boundary layer. -/
theorem RigidityHypotheses.distanceRecovery_integral_energy_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    {K : Set (Space d)} (hK : IsCompact K) :
    (∫ x in K, rescaledPhaseEnergyDensity f R (distanceRecovery f δ R E) x) ≤
      ∫ x in K ∩ {y | R * infDist y Eᶜ ∈ Ioo 0 (recoveryTravelTime f δ 1)},
        R * (2 * normalizedPotential f (distanceRecovery f δ R E x) + δ) :=
  hr.geometricRecoveryProfile_integral_energy_le h hδ hR (lipschitz_infDist_pt Eᶜ) hK

end SerrinEpigraph
