module

public import SerrinEpigraph.RadialGluing

/-!
# Finite endpoint limits for bounded radial systems
-/

public section
noncomputable section
open Set
open scoped NNReal Topology

namespace SerrinEpigraph

/-- A bounded slope makes a radial value Lipschitz on a convex interval. -/
theorem IsRadialSystemOn.value_lipschitzOn {m : ℕ} {f Q P : ℝ → ℝ} {S : Set ℝ}
    (h : IsRadialSystemOn m f Q P S) (hS : Convex ℝ S) {B : ℝ≥0}
    (hB : ∀ t ∈ S, ‖P t‖ ≤ B) : LipschitzOnWith B Q S := by
  apply hS.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht ↦ (h t ht).1.hasDerivWithinAt)
  intro t ht
  exact_mod_cast hB t ht

/-- Away from radius zero, bounded forcing and slope bound the slope derivative. -/
theorem radial_slope_rhs_norm_le {m : ℕ} {f Q P : ℝ → ℝ} {δ t : ℝ} {B M : ℝ≥0}
    (hδ : 0 < δ) (ht : δ ≤ t) (hB : ‖P t‖ ≤ B) (hM : ‖f (Q t)‖ ≤ M) :
    ‖-f (Q t) - (m : ℝ) / t * P t‖ ≤ M + (m : ℝ) / δ * B := by
  have htpos : 0 < t := hδ.trans_le ht
  calc
    _ ≤ ‖-f (Q t)‖ + ‖(m : ℝ) / t * P t‖ := norm_sub_le _ _
    _ = ‖f (Q t)‖ + ((m : ℝ) / t) * ‖P t‖ := by
      rw [norm_neg, norm_mul, Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg m) htpos.le)]
    _ ≤ M + ((m : ℝ) / δ) * B := by
      gcongr

/-- The slope has a uniform Lipschitz bound on intervals separated from radius zero. -/
theorem IsRadialSystemOn.slope_lipschitzOn {m : ℕ} {f Q P : ℝ → ℝ} {S : Set ℝ}
    (h : IsRadialSystemOn m f Q P S) (hS : Convex ℝ S) {δ : ℝ} (hδ : 0 < δ)
    (hrad : ∀ t ∈ S, δ ≤ t) {B M : ℝ≥0}
    (hB : ∀ t ∈ S, ‖P t‖ ≤ B) (hM : ∀ t ∈ S, ‖f (Q t)‖ ≤ M) :
    LipschitzOnWith ⟨M + (m : ℝ) / δ * B, by positivity⟩ P S := by
  apply hS.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht ↦ (h t ht).2.hasDerivWithinAt)
  intro t ht
  exact_mod_cast radial_slope_rhs_norm_le hδ (hrad t ht) (hB t ht) (hM t ht)

/-- A Lipschitz function on a radius interval has a finite limit at either endpoint. -/
theorem lipschitzOn_exists_endpoint_limit {F : ℝ → ℝ} {S : Set ℝ} {K : ℝ≥0}
    (hF : LipschitzOnWith K F S) (R : ℝ) :
    ∃ a : ℝ, Filter.Tendsto F (𝓝[S] R) (𝓝 a) := by
  obtain ⟨G, hG, heq⟩ := hF.extend_real
  refine ⟨G R, ?_⟩
  apply hG.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (heq ht).symm

/-- Bounded radial systems away from zero have finite value and slope limits at a finite endpoint. -/
theorem IsRadialSystemOn.exists_endpoint_limits {m : ℕ} {f Q P : ℝ → ℝ} {δ R : ℝ}
    (h : IsRadialSystemOn m f Q P (Ioo δ R)) (hδ : 0 < δ) {B M : ℝ≥0}
    (hB : ∀ t ∈ Ioo δ R, ‖P t‖ ≤ B) (hM : ∀ t ∈ Ioo δ R, ‖f (Q t)‖ ≤ M) :
    ∃ a p : ℝ, Filter.Tendsto Q (𝓝[Ioo δ R] R) (𝓝 a) ∧
      Filter.Tendsto P (𝓝[Ioo δ R] R) (𝓝 p) := by
  obtain ⟨a, ha⟩ := lipschitzOn_exists_endpoint_limit
    (h.value_lipschitzOn (convex_Ioo δ R) hB) R
  obtain ⟨p, hp⟩ := lipschitzOn_exists_endpoint_limit
    (h.slope_lipschitzOn (convex_Ioo δ R) hδ (fun _ ht ↦ ht.1.le) hB hM) R
  exact ⟨a, p, ha, hp⟩

/-- On the normalized value range, the project reaction is uniformly bounded. -/
theorem Hypotheses.reaction_norm_bound_on_unit_interval
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) : ∃ M : ℝ≥0, ∀ s ∈ Icc (0 : ℝ) 1, ‖f s‖ ≤ M := by
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    h.reaction_contDiffOn.continuousOn.mono (fun _ hs ↦ hs.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨⟨max M 0, le_max_right _ _⟩, fun s hs ↦ ?_⟩
  exact (hM s hs).trans (le_max_left _ _)

/-- A bounded-slope normalized radial system has finite limits under the original hypotheses. -/
theorem Hypotheses.radial_exists_endpoint_limits
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {Q P : ℝ → ℝ} {δ R : ℝ}
    (hQP : IsRadialSystemOn m f Q P (Ioo δ R)) (hδ : 0 < δ) {B : ℝ≥0}
    (hB : ∀ t ∈ Ioo δ R, ‖P t‖ ≤ B)
    (hval : ∀ t ∈ Ioo δ R, Q t ∈ Icc (0 : ℝ) 1) :
    ∃ a p : ℝ, Filter.Tendsto Q (𝓝[Ioo δ R] R) (𝓝 a) ∧
      Filter.Tendsto P (𝓝[Ioo δ R] R) (𝓝 p) := by
  obtain ⟨M, hM⟩ := h.reaction_norm_bound_on_unit_interval
  exact hQP.exists_endpoint_limits hδ hB (fun t ht ↦ hM (Q t) (hval t ht))

end SerrinEpigraph
