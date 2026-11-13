module

public import SerrinEpigraph.RadialEndpoint

/-!
# Energy bounds and finite endpoint limits without a slope-bound assumption
-/

public section
noncomputable section
open Set
open scoped NNReal Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- Radial energy decreases on every convex domain of positive radii and normalized values. -/
theorem Hypotheses.radial_energy_antitoneOn (h : Hypotheses g u f κ)
    {Q P : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hQP : IsRadialSystemOn m f Q P S) (hrad : ∀ t ∈ S, 0 < t)
    (hval : ∀ t ∈ S, Q t ∈ Ioo (0 : ℝ) 1) :
    AntitoneOn (radialEnergy f Q P) S := by
  have hQc : ContinuousOn Q S := fun t ht ↦ (hQP t ht).1.continuousAt.continuousWithinAt
  have hPc : ContinuousOn P S := fun t ht ↦ (hQP t ht).2.continuousAt.continuousWithinAt
  have hc : ContinuousOn (radialEnergy f Q P) S :=
    ((hPc.pow 2).div_const 2).sub (h.normalizedPotential_continuousOn.comp hQc
      (fun t ht ↦ ⟨(hval t ht).1.le, (hval t ht).2.le⟩))
  apply antitoneOn_of_hasDerivWithinAt_nonpos hS hc
    (f' := fun t ↦ -(m : ℝ) / t * P t ^ 2)
  · intro t ht
    have htS := interior_subset ht
    exact (h.radialEnergy_hasDerivAt (hQP t htS).1 (hQP t htS).2
      (hval t htS).1).hasDerivWithinAt
  · intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m))
        (hrad t (interior_subset ht)).le) (sq_nonneg _)

/-- Energy dissipation bounds the slope to the right of any interior positive radius. -/
theorem Hypotheses.radial_slope_bound_after (h : Hypotheses g u f κ)
    {Q P : ℝ → ℝ} {a δ R : ℝ} (ha : 0 ≤ a) (hδ : δ ∈ Ioo a R)
    (hQP : IsRadialSystemOn m f Q P (Ioo a R))
    (hval : ∀ t ∈ Ioo a R, Q t ∈ Ioo (0 : ℝ) 1) :
    ∃ B : ℝ≥0, ∀ t ∈ Ioo δ R, ‖P t‖ ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn h.normalizedPotential_continuousOn
  let D := |radialEnergy f Q P δ| + max C 0
  have hD : 0 ≤ D := add_nonneg (abs_nonneg _) (le_max_right _ _)
  refine ⟨⟨2 * D + 1, by positivity⟩, ?_⟩
  intro t ht
  have htS : t ∈ Ioo a R := ⟨hδ.1.trans ht.1, ht.2⟩
  have he := h.radial_energy_antitoneOn (convex_Ioo a R) hQP
    (fun s hs ↦ ha.trans_lt hs.1) hval hδ htS ht.1.le
  have hW : normalizedPotential f (Q t) ≤ max C 0 :=
    (le_abs_self _).trans ((hC (Q t) ⟨(hval t htS).1.le, (hval t htS).2.le⟩).trans
      (le_max_left _ _))
  have hE : radialEnergy f Q P δ ≤ |radialEnergy f Q P δ| := le_abs_self _
  have hs : P t ^ 2 ≤ 2 * D := by
    change P t ^ 2 / 2 - normalizedPotential f (Q t) ≤ radialEnergy f Q P δ at he
    dsimp only [D]
    linarith
  change ‖P t‖ ≤ 2 * D + 1
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (P t), sq_nonneg (|P t| - 1)]

/-- Normalized radial solutions have finite endpoint limits, without an assumed slope bound. -/
theorem Hypotheses.radial_endpoint_limits_of_normalized_values (h : Hypotheses g u f κ)
    {Q P : ℝ → ℝ} {a δ R : ℝ} (ha : 0 ≤ a) (hδ : δ ∈ Ioo a R)
    (hQP : IsRadialSystemOn m f Q P (Ioo a R))
    (hval : ∀ t ∈ Ioo a R, Q t ∈ Ioo (0 : ℝ) 1) :
    ∃ b p : ℝ, b ∈ Icc (0 : ℝ) 1 ∧ Filter.Tendsto Q (𝓝[<] R) (𝓝 b) ∧
      Filter.Tendsto P (𝓝[<] R) (𝓝 p) := by
  obtain ⟨B, hB⟩ := h.radial_slope_bound_after ha hδ hQP hval
  have hsub : Ioo δ R ⊆ Ioo a R := fun _ ht ↦ ⟨hδ.1.trans ht.1, ht.2⟩
  obtain ⟨b, p, hb, hp⟩ := h.radial_exists_endpoint_limits
    (hQP.mono hsub) (ha.trans_lt hδ.1) hB
    (fun t ht ↦ ⟨(hval t (hsub ht)).1.le, (hval t (hsub ht)).2.le⟩)
  let : Filter.NeBot (𝓝[Ioo δ R] R) := right_nhdsWithin_Ioo_neBot hδ.2
  have hbval : b ∈ Icc (0 : ℝ) 1 := isClosed_Icc.mem_of_tendsto hb (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨(hval t (hsub ht)).1.le, (hval t (hsub ht)).2.le⟩)
  rw [nhdsWithin_Ioo_eq_nhdsLT hδ.2] at hb hp
  exact ⟨b, p, hbval, hb, hp⟩

end SerrinEpigraph
