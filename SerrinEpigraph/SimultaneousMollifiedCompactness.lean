module

public import SerrinEpigraph.MollifiedPrimitiveCompactness

/-!
# Simultaneous uniform subsequences for countably many mollifications
-/

public section

open MeasureTheory Metric Filter
open scoped Topology BoundedContinuousFunction

namespace SerrinEpigraph

noncomputable section

/-- Countably many uniformly bounded Lipschitz families admit a common uniform subsequence. -/
theorem exists_simultaneous_uniform_subsequence
    {I : Type*} [Countable I] {X : I → Type*}
    [∀ i, PseudoMetricSpace (X i)] [∀ i, CompactSpace (X i)]
    (F : ∀ i, ℕ → X i →ᵇ ℝ) (C : I → NNReal) (M : I → ℝ)
    (hC : ∀ i n, LipschitzWith (C i) (F i n))
    (hM : ∀ i n x, F i n x ∈ Set.Icc 0 (M i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ v : X i →ᵇ ℝ,
      TendstoUniformly (fun n x ↦ F i (φ n) x) v atTop := by
  have hc (i : I) : IsCompact (closure (Set.range (F i))) := by
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc 0 (M i)) isCompact_Icc
    · intro v x hv
      obtain ⟨n, rfl⟩ := hv
      exact hM i n x
    · apply UniformEquicontinuous.equicontinuous
      apply Metric.uniformEquicontinuous_of_continuity_modulus (fun t : ℝ ↦ (C i : ℝ) * t)
      · simpa only [mul_zero, id_eq] using
          (tendsto_const_nhds.mul (tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0)))
      · intro x y v
        obtain ⟨n, hn⟩ := v.property
        rw [← hn]
        exact (hC i n).dist_le_mul x y
  let K (i : I) := closure (Set.range (F i))
  let : ∀ i, CompactSpace (K i) := fun i ↦ isCompact_iff_compactSpace.mp (hc i)
  let G : ℕ → ∀ i, K i := fun n i ↦ ⟨F i n, subset_closure (Set.mem_range_self n)⟩
  obtain ⟨v, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq G
  refine ⟨φ, hφ, fun i ↦ ⟨(v i).val, ?_⟩⟩
  have hi := continuous_subtype_val.continuousAt.tendsto.comp (tendsto_pi_nhds.mp ht i)
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hi

/-- One subsequence works for all mollification indices and all positive integer-radius balls. -/
theorem RigidityHypotheses.mollifiedPrimitive_simultaneous_subsequence
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (R : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n k : ℕ,
      ∃ v : (closedBall (0 : Space (m + 1)) (k + 1 : ℝ)) →ᵇ ℝ,
        TendstoUniformly (fun j (x : closedBall (0 : Space (m + 1)) (k + 1 : ℝ)) ↦
          mollify (fun y ↦ phasePrimitive f (zeroExtension g u (R (φ j) • y))) n x) v atTop := by
  let X (i : ℕ × ℕ) := closedBall (0 : Space (m + 1)) (i.2 + 1 : ℝ)
  let : ∀ i, CompactSpace (X i) := fun i ↦
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space (m + 1)) (i.2 + 1 : ℝ))
  have hv (j : ℕ) : Continuous (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) :=
    (hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul (R j))
  let F : ∀ i : ℕ × ℕ, ℕ → X i →ᵇ ℝ := fun i j ↦
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x ↦ mollify (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) i.1 x,
        (mollify_contDiff (hv j) i.1).continuous.comp continuous_subtype_val⟩
  have hC (i : ℕ × ℕ) := hr.mollifiedPrimitive_uniform_lipschitzOn h i.1 (i.2 + 1 : ℝ)
  choose C hC using hC
  have hM (i : ℕ × ℕ) (j : ℕ) (x : X i) : F i j x ∈ Set.Icc 0 (phasePrimitive f 1) := by
    have hb (y : Space (m + 1)) := h.phasePrimitive_mem_Icc
      ⟨h.zeroExtension_nonneg (R j • y), (hr.zeroExtension_lt_one (R j • y)).le⟩
    exact ⟨mollify_nonneg (fun y ↦ (hb y).1) i.1 x,
      mollify_le (hv j) (fun y ↦ (hb y).2) i.1 x⟩
  obtain ⟨φ, hφ, hlim⟩ := exists_simultaneous_uniform_subsequence F C
    (fun _ ↦ phasePrimitive f 1) (fun i j ↦ (hC i (R j)).to_restrict) hM
  exact ⟨φ, hφ, fun n k ↦ hlim (n, k)⟩

end

end SerrinEpigraph
