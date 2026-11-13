module

public import SerrinEpigraph.GraphPartition

/-!
# Finite weighted recovery profiles
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- Finite weighted combination of local competitors. -/
@[expose] noncomputable def partitionRecovery {ι : Type*} [Fintype ι] {d : ℕ}
    (η v : ι → Space d → ℝ) (x : Space d) : ℝ := ∑ i, η i x * v i x

/-- Subunit nonnegative weights preserve the normalized phase range. -/
theorem partitionRecovery_mem_Icc {ι : Type*} [Fintype ι] {d : ℕ}
    {η v : ι → Space d → ℝ} (hη : ∀ i x, 0 ≤ η i x)
    (hsum : ∀ x, ∑ i, η i x ≤ 1) (hv : ∀ i x, v i x ∈ Icc (0 : ℝ) 1)
    (x : Space d) : partitionRecovery η v x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hη i x) (hv i x).1)
  · exact (Finset.sum_le_sum (fun i _ ↦
      mul_le_of_le_one_right (hη i x) (hv i x).2)).trans (hsum x)

/-- Local profiles with the same positive phase retain that phase in L1 after
finite continuous partition gluing on a compact set. -/
theorem RigidityHypotheses.partitionRecovery_integral_limit
    {ι : Type*} [Fintype ι] {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ : ℝ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {δ R : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hR : ∀ j, 0 < R j)
    (hwidth : Tendsto (fun j ↦ recoveryTravelTime f (δ j) 1 / R j) atTop (𝓝 0))
    {η ρ : ι → Space d → ℝ} (hη : ∀ i, Continuous (η i))
    (hρ : ∀ i, Continuous (ρ i)) (hηpos : ∀ i x, 0 ≤ η i x)
    (hsum : ∀ x, ∑ i, η i x ≤ 1) {K E : Set (Space d)}
    (hK : IsCompact K) (hE : MeasurableSet E)
    (hone : ∀ x ∈ K, ∑ i, η i x = 1)
    (hphase : ∀ i x, x ∈ K → (0 < ρ i x ↔ x ∈ E)) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖partitionRecovery η (fun i ↦ geometricRecoveryProfile f (δ j) (R j) (ρ i)) x -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  classical
  let z := E.indicator (fun _ ↦ (1 : ℝ))
  let v := fun j i ↦ geometricRecoveryProfile f (δ j) (R j) (ρ i)
  have hz : Measurable z := measurable_const.indicator hE
  have hv (j : ℕ) (i : ι) : Continuous (v j i) :=
    (hr.recoveryProfile_lipschitz h (hδ j)).continuous.comp (continuous_const.mul (hρ i))
  have hp (j : ℕ) : Continuous (partitionRecovery η (v j)) :=
    continuous_finsetSum _ (fun i _ ↦ (hη i).mul (hv j i))
  have hval (j : ℕ) (x : Space d) : partitionRecovery η (v j) x ∈ Icc (0 : ℝ) 1 :=
    partitionRecovery_mem_Icc hηpos hsum
      (fun i x ↦ hr.geometricRecoveryProfile_mem_Icc h (hδ j) x) x
  have he := tendsto_integral_of_dominated_convergence (μ := volume.restrict K)
    (F := fun j x ↦ ‖partitionRecovery η (v j) x - z x‖)
    (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun j ↦ ((hp j).measurable.sub hz).norm.aestronglyMeasurable)
    (continuous_const.continuousOn.integrableOn_compact hK)
    (fun j ↦ Eventually.of_forall (fun x ↦ by
      have hx := hval j x
      simp only [Real.norm_eq_abs, abs_abs]
      apply abs_le.mpr
      by_cases hxE : x ∈ E <;> simp [z, hxE] <;> constructor <;> linarith [hx.1, hx.2]))
    (ae_restrict_of_forall_mem hK.measurableSet (fun x hx ↦ by
      have ht (i : ι) : Tendsto (fun j ↦ v j i x) atTop (𝓝 (z x)) := by
        simpa only [v, geometricRecoveryProfile, hphase i x hx, z, indicator_apply,
          Pi.one_apply] using hr.recoveryProfile_scaled_tendsto h hδ hR hwidth (ρ i x)
      have hs := tendsto_finsetSum Finset.univ (fun i _ ↦ (ht i).const_mul (η i x))
      have heq : (∑ i, η i x * z x) = z x := by rw [← Finset.sum_mul, hone x hx, one_mul]
      rw [heq] at hs
      simpa only [partitionRecovery, sub_self, norm_zero] using (hs.sub_const (z x)).norm))
  simpa only [integral_zero] using he

/-- Differentiating the weighted competitor separates profile gradients from weight gradients. -/
theorem gradient_partitionRecovery {ι : Type*} [Fintype ι] {d : ℕ}
    {η v : ι → Space d → ℝ} {x : Space d}
    (hη : ∀ i, DifferentiableAt ℝ (η i) x) (hv : ∀ i, DifferentiableAt ℝ (v i) x) :
    gradient (partitionRecovery η v) x =
      (∑ i, η i x • gradient (v i) x) + (∑ i, v i x • gradient (η i) x) := by
  classical
  unfold partitionRecovery gradient
  rw [fderiv_fun_sum (fun i _ ↦ (hη i).fun_mul (hv i)), map_sum]
  simp_rw [fderiv_fun_mul (hη _) (hv _), map_add, map_smul]
  rw [Finset.sum_add_distrib]

/-- The gradient contribution of the fixed weights is bounded uniformly over normalized profiles. -/
theorem norm_partition_weightGradient_le {ι : Type*} [Fintype ι] {d : ℕ}
    (η v : ι → Space d → ℝ) {x : Space d} (hv : ∀ i, v i x ∈ Icc (0 : ℝ) 1) :
    ‖∑ i, v i x • gradient (η i) x‖ ≤ ∑ i, ‖gradient (η i) x‖ := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Real.norm_of_nonneg (hv i).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (hv i).2

/-- The squared weight-gradient error vanishes after division by the blow-down scale. -/
theorem partition_weightGradient_integral_limit {ι : Type*} [Fintype ι] {d : ℕ}
    {η : ι → Space d → ℝ} (hη : ∀ i, ContDiff ℝ 1 (η i))
    {v : ℕ → ι → Space d → ℝ} (hv : ∀ j i, Continuous (v j i))
    (hval : ∀ j i x, v j i x ∈ Icc (0 : ℝ) 1)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRtop : Tendsto R atTop atTop)
    {K : Set (Space d)} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K, ‖∑ i, v j i x • gradient (η i) x‖ ^ 2 / R j)
      atTop (𝓝 0) := by
  classical
  have hg (i : ι) : Continuous (gradient (η i)) :=
    (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.comp
      ((hη i).continuous_fderiv one_ne_zero)
  have hb : Continuous (fun x ↦ (∑ i, ‖gradient (η i) x‖) ^ 2) :=
    (continuous_finsetSum _ (fun i _ ↦ (hg i).norm)).pow 2
  have ht := (tendsto_inv_atTop_zero.comp hRtop).const_mul
    (∫ x in K, (∑ i, ‖gradient (η i) x‖) ^ 2)
  simp only [mul_zero, Function.comp_def] at ht
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ div_nonneg (sq_nonneg _) (hR j).le)) _ ht
  intro j
  rw [← div_eq_mul_inv, ← integral_div]
  apply setIntegral_mono_on
    (((continuous_finsetSum _ (fun i _ ↦ (hv j i).smul (hg i))).norm.pow 2).div_const
      (R j) |>.continuousOn.integrableOn_compact hK)
    ((hb.div_const (R j)).continuousOn.integrableOn_compact hK) hK.measurableSet
  intro x _
  apply div_le_div_of_nonneg_right _ (hR j).le
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_partition_weightGradient_le η (v j)
    (fun i ↦ hval j i x)) 2

end SerrinEpigraph
