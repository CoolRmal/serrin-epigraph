module

public import SerrinEpigraph.RadialLocalFlow
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# A continuously differentiable extension across the zero reaction state
-/

public section
noncomputable section

open Set

namespace SerrinEpigraph

/-- Extend the right derivative constantly to negative arguments. -/
@[expose] def extendedReactionDerivative (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  derivWithin f (Ici 0) (max s 0)

/-- Integrating the extended derivative gives an extension of the reaction. -/
@[expose] def smoothReactionExtension (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  f 0 + ∫ t in (0 : ℝ)..s, extendedReactionDerivative f t

/-- The extended right derivative is continuous on the whole real line. -/
theorem extendedReactionDerivative_continuous {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Ici 0)) : Continuous (extendedReactionDerivative f) := by
  have hc := hf.continuousOn_derivWithin (uniqueDiffOn_Ici (0 : ℝ)) le_rfl
  apply continuousOn_univ.mp
  exact hc.comp (continuous_id.max continuous_const).continuousOn
    (fun s _ ↦ le_max_right s 0)

/-- The integral extension has the intended derivative everywhere, including zero. -/
theorem smoothReactionExtension_hasDerivAt {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Ici 0)) (s : ℝ) :
    HasDerivAt (smoothReactionExtension f) (extendedReactionDerivative f s) s := by
  have hc := extendedReactionDerivative_continuous hf
  convert
    (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_add (f 0) using 1
  rfl

/-- The extension is globally continuously differentiable. -/
theorem smoothReactionExtension_contDiff {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Ici 0)) : ContDiff ℝ 1 (smoothReactionExtension f) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s ↦ (smoothReactionExtension_hasDerivAt hf s).differentiableAt, ?_⟩
  have he : deriv (smoothReactionExtension f) = extendedReactionDerivative f :=
    funext fun s ↦ (smoothReactionExtension_hasDerivAt hf s).deriv
  rw [he]
  exact extendedReactionDerivative_continuous hf

/-- The extension agrees with the original reaction at all nonnegative states. -/
theorem smoothReactionExtension_eq {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Ici 0)) {s : ℝ} (hs : 0 ≤ s) :
    smoothReactionExtension f s = f s := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
    (hf.continuousOn.mono (fun _ ht ↦ ht.1)) (f' := extendedReactionDerivative f) ?_
    ((extendedReactionDerivative_continuous hf).intervalIntegrable 0 s)
  · dsimp only [smoothReactionExtension]
    rw [he]
    ring
  · intro t ht
    have hd := (hf.differentiableOn_one t ht.1.le).hasDerivWithinAt
    have hd' := hd.hasDerivAt (Ici_mem_nhds ht.1)
    simpa only [extendedReactionDerivative, max_eq_left ht.1.le] using hd'

/-- At a positive radius, the zero-state radial initial value problem has a local extension
whose equation agrees with the original equation wherever its value is nonnegative. -/
theorem exists_radial_system_from_zero {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Ici 0)) (m : ℕ) {a p : ℝ} (ha : 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Q P : ℝ → ℝ, Q a = 0 ∧ P a = p ∧
      (∀ t ∈ Ioo (a - ε) (a + ε),
        HasDerivAt Q (P t) t ∧
        HasDerivAt P (-smoothReactionExtension f (Q t) - (m : ℝ) / t * P t) t) ∧
      (∀ t ∈ Ioo (a - ε) (a + ε), 0 ≤ Q t →
        HasDerivAt P (-f (Q t) - (m : ℝ) / t * P t) t) := by
  obtain ⟨ε, hε, Q, P, hQ, hP, hd⟩ := exists_radial_system_at_positive_radius m
    (a := 0) (p := p) ha (smoothReactionExtension_contDiff hf).contDiffAt
  refine ⟨ε, hε, Q, P, hQ, hP, hd, ?_⟩
  intro t ht hQt
  simpa only [smoothReactionExtension_eq hf hQt] using (hd t ht).2

end SerrinEpigraph
