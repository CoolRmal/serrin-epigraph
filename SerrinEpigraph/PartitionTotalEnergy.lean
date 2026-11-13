module

public import SerrinEpigraph.RecoveryPositivePhase

/-!
# Complete energy comparison for finite partition recovery
-/

public section

open Set MeasureTheory

namespace SerrinEpigraph

/-- The kinetic density is bounded by normalized phase energy, including at the zero phase. -/
theorem RigidityHypotheses.kinetic_le_rescaledPhaseEnergy
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space d → ℝ} (hv : ∀ x, v x ∈ Icc (0 : ℝ) 1) {R : ℝ} (hR : 0 ≤ R)
    (x : Space d) : ‖gradient v x‖ ^ 2 / (2 * R) ≤ rescaledPhaseEnergyDensity f R v x := by
  rw [rescaledPhaseEnergyDensity_kinetic_potential f R hv x]
  exact le_add_of_nonneg_right (indicator_nonneg
    (fun y _ ↦ mul_nonneg hR (hr.normalizedPotential_nonneg h (hv y))) x)

/-- Integration preserves the full energy-defect decomposition on a common positive phase. -/
theorem Hypotheses.integral_partitionRecovery_energy_defect
    {ι : Type*} [Fintype ι] {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ R : ℝ} (h : Hypotheses g u f κ)
    {η v : ι → Space d → ℝ} (hη : ∀ i, LocallyLipschitz (η i))
    (hv : ∀ i, LocallyLipschitz (v i)) (hpos : ∀ i x, 0 ≤ η i x)
    (hsum : ∀ x, ∑ i, η i x ≤ 1) (hval : ∀ i x, v i x ∈ Icc (0 : ℝ) 1)
    {K : Set (Space d)} (hK : IsCompact K) (hone : ∀ x ∈ K, ∑ i, η i x = 1)
    {P : Space d → Prop} (hphase : ∀ x ∈ K, ∀ i, 0 < v i x ↔ P x) :
    (∫ x in K, rescaledPhaseEnergyDensity f R (partitionRecovery η v) x) -
        (∑ i, ∫ x in K, η i x * rescaledPhaseEnergyDensity f R (v i) x) =
      ((∫ x in K, ‖gradient (partitionRecovery η v) x‖ ^ 2 / (2 * R)) -
        ∑ i, ∫ x in K, η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) +
      (∫ x in K, R * (normalizedPotential f (partitionRecovery η v x) -
        ∑ i, η i x * normalizedPotential f (v i x))) := by
  classical
  have hp := partitionRecovery_locallyLipschitz hη hv
  have hpval := partitionRecovery_mem_Icc hpos hsum hval
  have hiE := h.integrableOn_rescaledPhaseEnergy hp hpval R hK
  have hiK := (integrableOn_gradient_sq_of_locallyLipschitz hp hK).div_const (2 * R)
  have hiEi (i : ι) : IntegrableOn (fun x ↦ η i x * rescaledPhaseEnergyDensity f R (v i) x) K := by
    simpa only [mul_comm] using IntegrableOn.mul_continuousOn
      (h.integrableOn_rescaledPhaseEnergy (hv i) (hval i) R hK) (hη i).continuous.continuousOn hK
  have hiKi (i : ι) : IntegrableOn (fun x ↦ η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) K := by
    simpa only [mul_comm] using IntegrableOn.mul_continuousOn
      ((integrableOn_gradient_sq_of_locallyLipschitz (hv i) hK).div_const (2 * R))
      (hη i).continuous.continuousOn hK
  have hiEs : IntegrableOn (fun x ↦ ∑ i, η i x * rescaledPhaseEnergyDensity f R (v i) x) K :=
    integrable_finsetSum _ (fun i _ ↦ hiEi i)
  have hiKs : IntegrableOn (fun x ↦ ∑ i, η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) K :=
    integrable_finsetSum _ (fun i _ ↦ hiKi i)
  have hwp : Continuous (fun x ↦ normalizedPotential f (partitionRecovery η v x)) :=
    h.normalizedPotential_continuousOn.comp_continuous hp.continuous hpval
  have hwv (i : ι) : Continuous (fun x ↦ normalizedPotential f (v i x)) :=
    h.normalizedPotential_continuousOn.comp_continuous (hv i).continuous (hval i)
  have hiD : IntegrableOn (fun x ↦ R * (normalizedPotential f (partitionRecovery η v x) -
      ∑ i, η i x * normalizedPotential f (v i x))) K :=
    (continuous_const.mul (hwp.sub (continuous_finsetSum _
      (fun i _ ↦ (hη i).continuous.mul (hwv i))))).continuousOn.integrableOn_compact hK
  have hiKd : IntegrableOn (fun x ↦ ‖gradient (partitionRecovery η v) x‖ ^ 2 / (2 * R) -
      ∑ i, η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) K := hiK.sub hiKs
  have he := setIntegral_congr_fun (μ := volume) hK.measurableSet (fun x hx ↦
    partitionRecovery_energy_defect f R hpos hsum hval (hone x hx) (hphase x hx))
  rw [integral_sub hiE hiEs, integral_add hiKd hiD,
    integral_sub hiK hiKs, integral_finsetSum _ (fun i _ ↦ hiEi i),
    integral_finsetSum _ (fun i _ ↦ hiKi i)] at he
  exact he

/-- Kinetic and potential error bounds combine into a full phase-energy comparison,
with the principal weighted patch energies counted once. -/
theorem RigidityHypotheses.integral_partitionRecovery_energy_le
    {ι : Type*} [Fintype ι] {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ R ε e D : ℝ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {η v : ι → Space d → ℝ} (hη : ∀ i, LocallyLipschitz (η i))
    (hv : ∀ i, LocallyLipschitz (v i)) (hpos : ∀ i x, 0 ≤ η i x)
    (hsum : ∀ x, ∑ i, η i x ≤ 1) (hval : ∀ i x, v i x ∈ Icc (0 : ℝ) 1)
    (hR : 0 ≤ R) (hε : 0 ≤ ε) {K : Set (Space d)} (hK : IsCompact K)
    (hone : ∀ x ∈ K, ∑ i, η i x = 1)
    {P : Space d → Prop} (hphase : ∀ x ∈ K, ∀ i, 0 < v i x ↔ P x)
    (hkin : (∫ x in K, ‖gradient (partitionRecovery η v) x‖ ^ 2 / (2 * R)) ≤
      (1 + ε) * (∑ i, ∫ x in K, η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) + e)
    (hpot : (∫ x in K, R * (normalizedPotential f (partitionRecovery η v x) -
      ∑ i, η i x * normalizedPotential f (v i x))) ≤ D) :
    (∫ x in K, rescaledPhaseEnergyDensity f R (partitionRecovery η v) x) ≤
      (1 + ε) * (∑ i, ∫ x in K, η i x * rescaledPhaseEnergyDensity f R (v i) x) + e + D := by
  classical
  have he := h.integral_partitionRecovery_energy_defect (R := R) hη hv hpos hsum hval hK hone hphase
  have hki : (∑ i, ∫ x in K, η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) ≤
      ∑ i, ∫ x in K, η i x * rescaledPhaseEnergyDensity f R (v i) x := by
    apply Finset.sum_le_sum
    intro i _
    have hiE : IntegrableOn (fun x ↦ η i x * rescaledPhaseEnergyDensity f R (v i) x) K := by
      simpa only [mul_comm] using IntegrableOn.mul_continuousOn
        (h.integrableOn_rescaledPhaseEnergy (hv i) (hval i) R hK) (hη i).continuous.continuousOn hK
    have hiK : IntegrableOn (fun x ↦ η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) K := by
      simpa only [mul_comm] using IntegrableOn.mul_continuousOn
        ((integrableOn_gradient_sq_of_locallyLipschitz (hv i) hK).div_const (2 * R))
        (hη i).continuous.continuousOn hK
    exact integral_mono hiK hiE (fun x ↦ mul_le_mul_of_nonneg_left
      (hr.kinetic_le_rescaledPhaseEnergy h (hval i) hR x) (hpos i x))
  nlinarith [mul_le_mul_of_nonneg_left hki hε]

end SerrinEpigraph
