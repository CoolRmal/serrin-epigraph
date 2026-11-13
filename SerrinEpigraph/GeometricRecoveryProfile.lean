module

public import SerrinEpigraph.RecoveryThickness
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Recovery profiles composed with geometric coordinates
-/

public section

open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SerrinEpigraph

/-- A transition profile pulled back along a signed geometric coordinate. -/
@[expose] noncomputable def geometricRecoveryProfile {d : ℕ} (f : ℝ → ℝ)
    (δ R : ℝ) (ρ : Space d → ℝ) (x : Space d) : ℝ :=
  recoveryProfile f δ (R * ρ x)

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ} {ρ : Space d → ℝ}

/-- Pullback preserves the normalized phase range. -/
theorem RigidityHypotheses.geometricRecoveryProfile_mem_Icc
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    (x : Space d) : geometricRecoveryProfile f δ R ρ x ∈ Icc (0 : ℝ) 1 :=
  hr.recoveryProfile_mem_Icc h hδ _

/-- A Lipschitz geometric coordinate gives a Lipschitz recovery competitor. -/
theorem RigidityHypotheses.geometricRecoveryProfile_lipschitz
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {C : ℝ≥0} (hρ : LipschitzWith C ρ) :
    LipschitzWith
      (⟨Real.sqrt (2 * (normalizedPotential f 0 + δ)), Real.sqrt_nonneg _⟩ * (‖R‖₊ * C))
      (geometricRecoveryProfile f δ R ρ) := by
  have hs : LipschitzWith (‖R‖₊ * C) (fun x ↦ R * ρ x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, ← mul_sub, norm_mul, Real.norm_eq_abs, abs_mul,
      NNReal.coe_mul, coe_nnnorm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hρ.dist_le_mul x y) (norm_nonneg R)
  exact (hr.recoveryProfile_lipschitz h hδ).comp hs

/-- On compact sets, the pulled-back profiles converge in L1 to the positive-coordinate phase. -/
theorem RigidityHypotheses.geometricRecoveryProfile_integral_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {δ R : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hR : ∀ j, 0 < R j)
    (hwidth : Tendsto (fun j ↦ recoveryTravelTime f (δ j) 1 / R j) atTop (𝓝 0))
    (hρ : Continuous ρ) {K : Set (Space d)} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖geometricRecoveryProfile f (δ j) (R j) ρ x -
        {x | 0 < ρ x}.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  let z : Space d → ℝ := {x | 0 < ρ x}.indicator (fun _ ↦ (1 : ℝ))
  have hz : Measurable z := measurable_const.indicator (isOpen_lt continuous_const hρ).measurableSet
  have hv (j : ℕ) : Continuous (geometricRecoveryProfile f (δ j) (R j) ρ) :=
    (hr.recoveryProfile_lipschitz h (hδ j)).continuous.comp (continuous_const.mul hρ)
  have hb : IntegrableOn (fun _ : Space d ↦ (1 : ℝ)) K :=
    continuous_const.continuousOn.integrableOn_compact hK
  have he := tendsto_integral_of_dominated_convergence (μ := volume.restrict K)
    (F := fun j x ↦ ‖geometricRecoveryProfile f (δ j) (R j) ρ x - z x‖)
    (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun j ↦ ((hv j).measurable.sub hz).norm.aestronglyMeasurable) hb
    (fun j ↦ Eventually.of_forall (fun x ↦ by
      have hx := hr.geometricRecoveryProfile_mem_Icc h (hδ j) (R := R j) (ρ := ρ) x
      simp only [Real.norm_eq_abs, abs_abs]
      apply abs_le.mpr
      by_cases hs : 0 < ρ x <;> simp [z, hs] <;> constructor <;> linarith [hx.1, hx.2]))
    (Eventually.of_forall (fun x ↦ by
      have ht := (hr.recoveryProfile_scaled_tendsto h hδ hR hwidth (ρ x)).sub_const (z x)
      have hzval : z x = if 0 < ρ x then 1 else 0 := by simp [z, indicator_apply]
      simpa only [geometricRecoveryProfile, hzval, sub_self, norm_zero] using ht.norm))
  simpa only [integral_zero] using he

end SerrinEpigraph
