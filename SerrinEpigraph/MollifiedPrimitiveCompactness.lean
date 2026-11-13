module

public import SerrinEpigraph.MollificationFamilyBounds
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences

/-!
# Convergent subsequences at a fixed mollification scale
-/

public section

open MeasureTheory Metric Filter
open scoped Topology BoundedContinuousFunction

namespace SerrinEpigraph

noncomputable section

/-- A uniformly Lipschitz, uniformly bounded sequence on a compact metric space has a uniform limit
along a strictly increasing subsequence. -/
theorem exists_uniform_subsequence_of_lipschitz
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (F : ℕ → X →ᵇ ℝ) (C : NNReal) (M : ℝ)
    (hC : ∀ n, LipschitzWith C (F n)) (hM : ∀ n x, F n x ∈ Set.Icc 0 M) :
    ∃ v : X →ᵇ ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun n x ↦ F (φ n) x) v atTop := by
  have he : Equicontinuous ((↑) : Set.range F → X → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply Metric.uniformEquicontinuous_of_continuity_modulus (fun t : ℝ ↦ (C : ℝ) * t)
    · simpa only [mul_zero, id_eq] using
        (tendsto_const_nhds.mul (tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0)))
    · intro x y i
      obtain ⟨n, hn⟩ := i.property
      rw [← hn]
      exact (hC n).dist_le_mul x y
  have hc := BoundedContinuousFunction.arzela_ascoli (Set.Icc 0 M) isCompact_Icc
    (Set.range F) (fun v x hv ↦ by obtain ⟨n, rfl⟩ := hv; exact hM n x) he
  obtain ⟨v, _, φ, hφ, ht⟩ := hc.tendsto_subseq
    (fun n ↦ subset_closure (Set.mem_range_self n))
  exact ⟨v, φ, hφ, BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ht⟩

/-- Any sequence of dilations has a uniformly convergent mollified primitive subsequence on a fixed
ball, for each fixed mollification index. -/
theorem RigidityHypotheses.mollifiedPrimitive_uniform_subsequence
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (n : ℕ) (r : ℝ) (R : ℕ → ℝ) :
    ∃ v : (closedBall (0 : Space (m + 1)) r) →ᵇ ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun j (x : closedBall (0 : Space (m + 1)) r) ↦
        mollify (fun y ↦ phasePrimitive f (zeroExtension g u (R (φ j) • y))) n x) v atTop := by
  let : CompactSpace (closedBall (0 : Space (m + 1)) r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space (m + 1)) r)
  have hv (j : ℕ) : Continuous (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) :=
    (hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul (R j))
  let F : ℕ → (closedBall (0 : Space (m + 1)) r) →ᵇ ℝ := fun j ↦
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x ↦ mollify (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) n x,
        (mollify_contDiff (hv j) n).continuous.comp continuous_subtype_val⟩
  obtain ⟨C, hC⟩ := hr.mollifiedPrimitive_uniform_lipschitzOn h n r
  apply exists_uniform_subsequence_of_lipschitz F C (phasePrimitive f 1)
  · intro j
    exact (hC (R j)).to_restrict
  · intro j x
    have hb (y : Space (m + 1)) := h.phasePrimitive_mem_Icc
      ⟨h.zeroExtension_nonneg (R j • y), (hr.zeroExtension_lt_one (R j • y)).le⟩
    exact ⟨mollify_nonneg (fun y ↦ (hb y).1) n x,
      mollify_le (hv j) (fun y ↦ (hb y).2) n x⟩

end

end SerrinEpigraph
