module

public import SerrinEpigraph.PartitionKineticIntegral

/-!
# Positive phases and energy decomposition for recovery mixtures
-/

public section

open Set

namespace SerrinEpigraph

/-- The extended recovery profile is positive exactly at positive times. -/
theorem RigidityHypotheses.recoveryProfile_pos_iff
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ δ t : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    0 < recoveryProfile f δ t ↔ 0 < t := by
  constructor
  · intro hp
    by_contra ht
    rw [hr.recoveryProfile_eq_zero h hδ (le_of_not_gt ht)] at hp
    exact lt_irrefl _ hp
  · intro ht
    by_cases he : t < recoveryTravelTime f δ 1
    · rw [recoveryProfile_eq_core ⟨ht.le, he.le⟩]
      exact (hr.recoveryProfileCore_mem_Ioo h hδ ⟨ht, he⟩).1
    · rw [hr.recoveryProfile_eq_one h hδ (le_of_not_gt he)]
      norm_num

/-- A convex mixture of nonnegative components with a common positive phase retains it. -/
theorem partitionRecovery_pos_iff {ι : Type*} [Fintype ι] {d : ℕ}
    {η v : ι → Space d → ℝ} {x : Space d} {P : Prop}
    (hη : ∀ i, 0 ≤ η i x) (hv : ∀ i, 0 ≤ v i x)
    (hsum : ∑ i, η i x = 1) (hphase : ∀ i, 0 < v i x ↔ P) :
    0 < partitionRecovery η v x ↔ P := by
  classical
  constructor
  · intro hp
    by_contra hn
    have hz (i : ι) : v i x = 0 := le_antisymm (le_of_not_gt (fun hi ↦ hn ((hphase i).mp hi))) (hv i)
    simp [partitionRecovery, hz] at hp
  · intro hp
    obtain ⟨i, hi, hip⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hη i)).mp
      (show 0 < ∑ i, η i x by rw [hsum]; norm_num)
    exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (hη j) (hv j))
      ⟨i, hi, mul_pos hip ((hphase i).mpr hp)⟩

/-- Graph recovery mixtures have precisely the original epigraph as their positive phase
where their nonnegative weights add up to one. -/
theorem RigidityHypotheses.graph_partitionRecovery_pos_iff
    {ι : Type*} [Fintype ι] {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ δ R : ℝ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) {b : Space d → ℝ} {L : ι → ℝ}
    (hL : ∀ i, 0 < L i) {η : ι → Space (d + 1) → ℝ} {x : Space (d + 1)}
    (hη : ∀ i, 0 ≤ η i x) (hsum : ∑ i, η i x = 1) :
    0 < partitionRecovery η (fun i y ↦ recoveryProfile f δ (R * graphHeight b y / L i)) x ↔
      x ∈ epigraph b := by
  apply partitionRecovery_pos_iff hη (fun i ↦ (hr.recoveryProfile_mem_Icc h hδ _).1) hsum
  intro i
  rw [hr.recoveryProfile_pos_iff h hδ, div_pos_iff_of_pos_right (hL i),
    mul_pos_iff_of_pos_left hR]
  exact sub_pos

/-- The phase indicator can be removed from the kinetic part of normalized energy. -/
theorem rescaledPhaseEnergyDensity_kinetic_potential {d : ℕ}
    (f : ℝ → ℝ) (R : ℝ) {v : Space d → ℝ} (hv : ∀ y, v y ∈ Icc (0 : ℝ) 1)
    (x : Space d) :
    rescaledPhaseEnergyDensity f R v x = ‖gradient v x‖ ^ 2 / (2 * R) +
      {y | 0 < v y}.indicator (fun y ↦ R * normalizedPotential f (v y)) x := by
  by_cases hx : 0 < v x
  · simp [rescaledPhaseEnergyDensity, hx]
  · have hz : v x = 0 := le_antisymm (le_of_not_gt hx) (hv x).1
    have hg := gradient_cutoff_eq_zero_of_endpoint hv (Or.inl hz)
    simp [rescaledPhaseEnergyDensity, hx, hg]

/-- With a common positive phase, the full energy defect is the kinetic defect plus
the ordinary potential defect; zero-phase contributions cancel using total weight one. -/
theorem partitionRecovery_energy_defect {ι : Type*} [Fintype ι] {d : ℕ}
    (f : ℝ → ℝ) (R : ℝ) {η v : ι → Space d → ℝ}
    (hη : ∀ i y, 0 ≤ η i y) (hsum : ∀ y, ∑ i, η i y ≤ 1)
    (hv : ∀ i y, v i y ∈ Icc (0 : ℝ) 1) {x : Space d} {P : Prop}
    (hone : ∑ i, η i x = 1) (hphase : ∀ i, 0 < v i x ↔ P) :
    rescaledPhaseEnergyDensity f R (partitionRecovery η v) x -
        (∑ i, η i x * rescaledPhaseEnergyDensity f R (v i) x) =
      (‖gradient (partitionRecovery η v) x‖ ^ 2 / (2 * R) -
        ∑ i, η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) +
      R * (normalizedPotential f (partitionRecovery η v x) -
        ∑ i, η i x * normalizedPotential f (v i x)) := by
  classical
  have hp := partitionRecovery_pos_iff (fun i ↦ hη i x) (fun i ↦ (hv i x).1) hone hphase
  have hval := partitionRecovery_mem_Icc hη hsum hv
  rw [rescaledPhaseEnergyDensity_kinetic_potential f R hval x]
  simp_rw [rescaledPhaseEnergyDensity_kinetic_potential f R (hv _) x]
  by_cases hP : P
  · have hpx : 0 < partitionRecovery η v x := hp.mpr hP
    have hvx (i : ι) : 0 < v i x := (hphase i).mpr hP
    simp only [indicator_apply, mem_ofPred_eq, hpx, hvx, ite_true,
      mul_add, Finset.sum_add_distrib, mul_left_comm _ R, ← Finset.mul_sum]
    ring
  · have hpx : ¬0 < partitionRecovery η v x := fun hh ↦ hP (hp.mp hh)
    have hvx (i : ι) : ¬0 < v i x := fun hh ↦ hP ((hphase i).mp hh)
    have hz (i : ι) : v i x = 0 := le_antisymm (le_of_not_gt (hvx i)) (hv i x).1
    have hpz : partitionRecovery η v x = 0 := le_antisymm (le_of_not_gt hpx) (hval x).1
    simp only [indicator_apply, mem_ofPred_eq, lt_self_iff_false, ite_false, add_zero,
      hpz, hz, ← Finset.sum_mul, hone, one_mul, sub_self, mul_zero]

end SerrinEpigraph
