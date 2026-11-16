module

public import SerrinEpigraph.DiffuseTiltConvergence
public import SerrinEpigraph.SurfaceEnergyMonotonicity

/-!
# Exact all-center bounds from the asymptotic surface mass
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Monotonicity at every center and a finite origin-centered mass limit give the
same exact upper bound at every center and every positive radius. -/
theorem integral_closedBall_le_asymptotic_surface_mass {d m : ℕ} {q : Space d → ℝ}
    (hq : ∀ x, 0 ≤ q x) (hi : ∀ K : Set (Space d), IsCompact K → IntegrableOn q K)
    (hmono : ∀ c : Space d,
      MonotoneOn (fun r ↦ r ^ (-(m : ℤ)) * ∫ x in closedBall c r, q x) (Ioi 0))
    {L : ℝ} (hL : Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * ∫ x in closedBall 0 r, q x)
      atTop (𝓝 L)) (c : Space d) {r : ℝ} (hr : 0 < r) :
    (∫ x in closedBall c r, q x) ≤ L * r ^ m := by
  have hshift : Tendsto (fun R : ℝ ↦ R + ‖c‖) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b - ‖c‖, fun R hR ↦ by linarith⟩
  have hratio : Tendsto (fun R : ℝ ↦ (1 + ‖c‖ / R) ^ m) atTop (𝓝 1) := by
    simpa only [add_zero, one_pow, id_eq] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := ‖c‖)).div_atTop tendsto_id)).pow m
  have ht := hratio.mul (hL.comp hshift)
  simp only [one_mul] at ht
  have hbound : r ^ (-(m : ℤ)) * (∫ x in closedBall c r, q x) ≤ L := by
    apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop r] with R hR
    have hR0 : 0 < R := hr.trans_le hR
    have hT0 : 0 < R + ‖c‖ := add_pos_of_pos_of_nonneg hR0 (norm_nonneg c)
    have hsub : closedBall c R ⊆ closedBall 0 (R + ‖c‖) :=
      closedBall_subset_closedBall' (by rw [dist_zero_right])
    have hm := hmono c hr hR0 hR
    have hiR := setIntegral_mono_set (hi _ (isCompact_closedBall 0 (R + ‖c‖)))
      (Eventually.of_forall hq) (Eventually.of_forall hsub)
    have hh := mul_le_mul_of_nonneg_left hiR (zpow_nonneg hR0.le (-(m : ℤ)))
    calc
      _ ≤ R ^ (-(m : ℤ)) * ∫ x in closedBall c R, q x := hm
      _ ≤ R ^ (-(m : ℤ)) * ∫ x in closedBall 0 (R + ‖c‖), q x := hh
      _ = (1 + ‖c‖ / R) ^ m *
          ((R + ‖c‖) ^ (-(m : ℤ)) * ∫ x in closedBall 0 (R + ‖c‖), q x) := by
        rw [show 1 + ‖c‖ / R = (R + ‖c‖) / R by field_simp,
          div_pow, zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
        field_simp
  rw [zpow_neg, zpow_natCast] at hbound
  have hh := mul_le_mul_of_nonneg_left hbound (pow_nonneg hr.le m)
  have he : r ^ m * ((r ^ m)⁻¹ * ∫ x in closedBall c r, q x) =
      ∫ x in closedBall c r, q x := by field_simp
  rw [he] at hh
  simpa only [mul_comm] using hh

/-- The original Serrin solution satisfies the exact all-center surface bound
corresponding to its asymptotic origin energy coefficient. -/
theorem RigidityHypotheses.phaseEnergy_le_asymptotic_mass
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hL : Tendsto (fun R : ℝ ↦ R ^ (-(m : ℤ)) * ∫ x in closedBall 0 R,
      phaseEnergyDensity f 0 (zeroExtension g u) x) atTop (𝓝 L))
    (c : Space (m + 1)) {r : ℝ} (hradius : 0 < r) :
    (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m :=
  integral_closedBall_le_asymptotic_surface_mass (hr.phaseEnergy_zeroExtension_nonneg h le_rfl)
    (fun _ hK ↦ hr.integrableOn_phaseEnergy_zeroExtension h 0 hK)
    (hr.surface_scaled_energy_monotone h) hL c hradius

end SerrinEpigraph
