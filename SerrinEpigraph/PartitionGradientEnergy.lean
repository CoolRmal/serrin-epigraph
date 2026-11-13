module

public import SerrinEpigraph.PartitionRecovery
public import SerrinEpigraph.GluingGradientEnergy

/-!
# Quadratic gradient energy of finite partition recovery
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- Nonnegative weights of total mass at most one satisfy the quadratic norm inequality. -/
theorem norm_weighted_sum_sq_le {ι : Type*} [Fintype ι] {d : ℕ}
    (w : ι → ℝ) (a : ι → Space d) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ 1) :
    ‖∑ i, w i • a i‖ ^ 2 ≤ ∑ i, w i * ‖a i‖ ^ 2 := by
  classical
  have hn : ‖∑ i, w i • a i‖ ≤ ∑ i, w i * ‖a i‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg (hw _)] using
      norm_sum_le Finset.univ (fun i ↦ w i • a i)
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i ↦ w i * ‖a i‖) (f := w) (g := fun i ↦ w i * ‖a i‖ ^ 2)
    (fun i _ ↦ hw i) (fun i _ ↦ mul_nonneg (hw i) (sq_nonneg _))
    (fun i _ ↦ le_of_eq (by ring))
  exact ((pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc).trans
    (mul_le_of_le_one_left (Finset.sum_nonneg (fun i _ ↦
      mul_nonneg (hw i) (sq_nonneg _))) hs)

/-- The principal gradient energy has arbitrarily small multiplicative loss,
with a separate squared weight-gradient error. -/
theorem norm_gradient_partitionRecovery_sq_le {ι : Type*} [Fintype ι] {d : ℕ}
    {η v : ι → Space d → ℝ} {x : Space d}
    (hη : ∀ i, DifferentiableAt ℝ (η i) x) (hv : ∀ i, DifferentiableAt ℝ (v i) x)
    (hpos : ∀ i, 0 ≤ η i x) (hsum : ∑ i, η i x ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ‖gradient (partitionRecovery η v) x‖ ^ 2 ≤
      (1 + ε) * (∑ i, η i x * ‖gradient (v i) x‖ ^ 2) +
        (1 + 1 / ε) * ‖∑ i, v i x • gradient (η i) x‖ ^ 2 := by
  rw [gradient_partitionRecovery hη hv]
  exact ((pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans
    (add_sq_le_with_parameter _ _ hε)).trans
    (add_le_add (mul_le_mul_of_nonneg_left
      (norm_weighted_sum_sq_le (fun i ↦ η i x) (fun i ↦ gradient (v i) x) hpos hsum)
      (show 0 ≤ 1 + ε by linarith)) le_rfl)

/-- The finite partition gradient estimate with the diffuse-energy coefficient. -/
theorem partitionRecovery_kinetic_energy_le {ι : Type*} [Fintype ι] {d : ℕ}
    {η v : ι → Space d → ℝ} {x : Space d}
    (hη : ∀ i, DifferentiableAt ℝ (η i) x) (hv : ∀ i, DifferentiableAt ℝ (v i) x)
    (hpos : ∀ i, 0 ≤ η i x) (hsum : ∑ i, η i x ≤ 1)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ‖gradient (partitionRecovery η v) x‖ ^ 2 / (2 * R) ≤
      (1 + ε) * (∑ i, η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) +
        (1 + 1 / ε) * ‖∑ i, v i x • gradient (η i) x‖ ^ 2 / (2 * R) := by
  have he := div_le_div_of_nonneg_right
    (norm_gradient_partitionRecovery_sq_le hη hv hpos hsum hε)
    (show 0 ≤ 2 * R by positivity)
  convert he using 1
  simp only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  ring

/-- The kinetic estimate applies almost everywhere to locally Lipschitz patch profiles. -/
theorem partitionRecovery_kinetic_energy_le_ae {ι : Type*} [Fintype ι] {d : ℕ}
    {η v : ι → Space d → ℝ} (hη : ∀ i, LocallyLipschitz (η i))
    (hv : ∀ i, LocallyLipschitz (v i)) (hpos : ∀ i x, 0 ≤ η i x)
    (hsum : ∀ x, ∑ i, η i x ≤ 1) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∀ᵐ x ∂volume, ‖gradient (partitionRecovery η v) x‖ ^ 2 / (2 * R) ≤
      (1 + ε) * (∑ i, η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) +
        (1 + 1 / ε) * ‖∑ i, v i x • gradient (η i) x‖ ^ 2 / (2 * R) := by
  have hηae := ae_all_iff.mpr (fun i ↦ ae_differentiableAt_of_locallyLipschitz (hη i))
  have hvae := ae_all_iff.mpr (fun i ↦ ae_differentiableAt_of_locallyLipschitz (hv i))
  filter_upwards [hηae, hvae] with x hxη hxv
  exact partitionRecovery_kinetic_energy_le hxη hxv (fun i ↦ hpos i x) (hsum x) hε hR

end SerrinEpigraph
