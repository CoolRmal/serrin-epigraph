module

public import SerrinEpigraph.LocalPrimitiveLimits

/-!
# Compatibility of local integral limits
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- Local integral convergence restricts to smaller sets. -/
theorem integral_limit_mono_set {d : ℕ} {S T : Set (Space d)} (hST : S ⊆ T)
    (F : ℕ → Space d → ℝ) (v : Space d → ℝ)
    (hF : ∀ j, IntegrableOn (F j) T) (hv : IntegrableOn v T)
    (ht : Tendsto (fun j ↦ ∫ x in T, ‖F j x - v x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in S, ‖F j x - v x‖) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro j
    exact integral_nonneg (fun x ↦ norm_nonneg _)
  · intro j
    exact setIntegral_mono_set ((hF j).sub hv).norm
      (Eventually.of_forall (fun x ↦ norm_nonneg _)) (Eventually.of_forall hST)

/-- Two integral limits of the same sequence agree almost everywhere. -/
theorem ae_eq_of_integral_limits {d : ℕ} {S : Set (Space d)}
    (F : ℕ → Space d → ℝ) {v w : Space d → ℝ}
    (hF : ∀ j, IntegrableOn (F j) S) (hv : IntegrableOn v S) (hw : IntegrableOn w S)
    (htv : Tendsto (fun j ↦ ∫ x in S, ‖F j x - v x‖) atTop (𝓝 0))
    (htw : Tendsto (fun j ↦ ∫ x in S, ‖F j x - w x‖) atTop (𝓝 0)) :
    v =ᵐ[volume.restrict S] w := by
  have ht := htv.add htw
  simp only [zero_add] at ht
  have hle : (∫ x in S, ‖v x - w x‖) ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    exact Eventually.of_forall (fun j ↦ by
      have he := integral_norm_sub_triangle hv (hF j) hw
      simpa only [norm_sub_rev (v _) (F j _)] using he)
  have hz : (∫ x in S, ‖v x - w x‖) = 0 :=
    le_antisymm hle (integral_nonneg (fun x ↦ norm_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun x ↦ norm_nonneg (v x - w x))) (hv.sub hw).norm).mp hz
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (norm_eq_zero.mp hx)

/-- The phase primitive has compatible local limits on nested integer-radius balls. -/
theorem RigidityHypotheses.phasePrimitive_compatible_local_limits
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : ℕ → Space (m + 1) → ℝ,
      (∀ k : ℕ, IntegrableOn (V k) (closedBall 0 (k + 1 : ℝ))) ∧
      (∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
        ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) - V k x‖) atTop (𝓝 0)) ∧
      (∀ k l : ℕ, k ≤ l → V k =ᵐ[volume.restrict (closedBall 0 (k + 1 : ℝ))] V l) := by
  obtain ⟨φ, hφ, hlim⟩ := hr.phasePrimitive_local_integral_limits h R hR
  choose V hV hlim using hlim
  refine ⟨φ, hφ, V, hV, hlim, fun k l hkl ↦ ?_⟩
  have hsub : closedBall (0 : Space (m + 1)) (k + 1 : ℝ) ⊆ closedBall 0 (l + 1 : ℝ) :=
    closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hkl 1)
  have hF (j : ℕ) (q : ℕ) : IntegrableOn
      (fun x ↦ phasePrimitive f (zeroExtension g u (R (φ j) • x)))
      (closedBall 0 (q + 1 : ℝ)) :=
    ((hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul (R (φ j)))).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 (q + 1 : ℝ))
  exact ae_eq_of_integral_limits _ (fun j ↦ hF j k) (hV k) ((hV l).mono_set hsub)
    (hlim k) (integral_limit_mono_set hsub _ _ (fun j ↦ hF j l) (hV l) (hlim l))

end SerrinEpigraph
