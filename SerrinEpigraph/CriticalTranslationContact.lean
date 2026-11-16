module

public import SerrinEpigraph.StableWellTranslation
public import SerrinEpigraph.PhysicalTranslationCompactness

/-!
# A critical translation contact below the equilibrium

Failure points approaching the boundary of the full-space translation order set
give a locally uniform translated limit with equal values at the two contact
points, strictly below the stable equilibrium.
-/

public section

noncomputable section

open Set Filter Metric
open scoped Topology NNReal

namespace SerrinEpigraph

/-- The global Lipschitz bound allows the evaluation point to move in a
locally convergent sequence of physical translations. -/
theorem translates_tendsto_at_moving_point {d : ℕ} {U V : Space d → ℝ} {L : ℝ≥0}
    (hU : LipschitzWith L U) {p a : ℕ → Space d} {a₀ : Space d}
    (ha : Tendsto a atTop (𝓝 a₀))
    (hlim : Tendsto (fun j ↦ U (p j + a₀)) atTop (𝓝 (V a₀))) :
    Tendsto (fun j ↦ U (p j + a j)) atTop (𝓝 (V a₀)) := by
  have hd : Tendsto (fun j ↦ dist (U (p j + a j)) (U (p j + a₀))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ dist_nonneg)
      (fun j ↦ by simpa only [dist_add_left] using hU.dist_le_mul (p j + a j) (p j + a₀))
    simpa using (tendsto_const_nhds (x := (L : ℝ))).mul
      (ha.dist (tendsto_const_nhds (x := a₀)))
  exact tendsto_of_tendsto_of_dist hlim (by simpa only [dist_comm] using hd)

/-- Every boundary point of the translation order set is the limit of disallowed
translations, with a locally uniform contact limit below one uniform threshold. -/
theorem RigidityHypotheses.exists_critical_translation_contact
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ b : ℝ, b ∈ Ioo 0 1 ∧ ∀ a₀ ∈ frontier (translationOrderSet (zeroExtension g u)),
      ∃ (a p : ℕ → Space (m + 1)) (V : Space (m + 1) → ℝ),
        Tendsto a atTop (𝓝 a₀) ∧
        (∀ j, a j ∉ translationOrderSet (zeroExtension g u)) ∧
        (∀ j, zeroExtension g u (p j + a j) < zeroExtension g u (p j) ∧
          zeroExtension g u (p j + a j) ≤ b) ∧
        LipschitzWith ⟨κ, h.kappa_pos.le⟩ V ∧ (∀ x, V x ∈ Icc 0 1) ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K) ∧
        translationOrderSet (zeroExtension g u) ⊆ translationOrderSet V ∧
        V a₀ = V 0 ∧ V 0 ≤ b := by
  obtain ⟨b, hb, hfailure⟩ := hr.exists_low_failure_threshold h
  refine ⟨b, hb, fun a₀ ha₀ ↦ ?_⟩
  have hclosed := isClosed_translationOrderSet h.zeroExtension_continuous
  have ha₀K := hclosed.frontier_subset ha₀
  have ha₀cl : a₀ ∈ closure (translationOrderSet (zeroExtension g u))ᶜ := by
    rw [frontier_eq_closure_inter_closure] at ha₀
    exact ha₀.2
  obtain ⟨a, haK, hat⟩ := mem_closure_iff_seq_limit.mp ha₀cl
  choose p hfail hbnd using fun j ↦ hfailure (a j) (haK j)
  obtain ⟨φ, V, hφ, hV, hval, hlim, horder⟩ := hr.exists_physical_translation_limit h p
  have hpt (x : Space (m + 1)) :
      Tendsto (fun j ↦ zeroExtension g u (p (φ j) + x)) atTop (𝓝 (V x)) :=
    (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hat' : Tendsto (fun j ↦ a (φ j)) atTop (𝓝 a₀) := hat.comp hφ.tendsto_atTop
  have heq := contact_eq_of_failed_translations (hr.zeroExtension_lipschitzWith h)
    hat' ha₀K (fun j ↦ hfail (φ j)) hpt
  refine ⟨fun j ↦ a (φ j), fun j ↦ p (φ j), V, hat', fun j ↦ haK (φ j),
    fun j ↦ ⟨hfail (φ j), hbnd (φ j)⟩, hV, hval, hlim, horder, heq, ?_⟩
  rw [← heq]
  apply le_of_tendsto (translates_tendsto_at_moving_point
    (hr.zeroExtension_lipschitzWith h) hat' (hpt a₀))
  exact Eventually.of_forall (fun j ↦ hbnd (φ j))

end SerrinEpigraph
