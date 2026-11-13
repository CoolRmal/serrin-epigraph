module

public import SerrinEpigraph.Reaction
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Linear upper bounds on a negative reaction tail
-/

public section

open scoped Topology

namespace SerrinEpigraph

/-- The slope of the reaction at a positive threshold bounds every later reaction value. -/
theorem reaction_le_slope_mul {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0))
    (hstructure : ∀ s : ℝ, 0 < s → 0 ≤ f s - s * deriv f s)
    {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) :
    f s ≤ (f s₀ / s₀) * s := by
  exact (div_le_iff₀ (hs₀.trans_le hs)).mp
    (antitoneOn_reaction_div hf hstructure hs₀ (hs₀.trans_le hs) hs)

/-- Continuity and the structure condition force a nonnegative reaction at zero. -/
theorem reaction_nonneg_zero {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0))
    (hstructure : ∀ s : ℝ, 0 < s → 0 ≤ f s - s * deriv f s) : 0 ≤ f 0 := by
  let t := fun n : ℕ ↦ (1 : ℝ) / (n + 1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have htlim : Filter.Tendsto t Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htf : Filter.Tendsto (fun n ↦ f (t n)) Filter.atTop (𝓝 (f 0)) := by
    apply (hf.continuousOn (0 : ℝ) (by simp)).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨htlim, Filter.Eventually.of_forall fun n ↦ (ht n).le⟩
  have hleft : Filter.Tendsto (fun n ↦ f 1 * t n) Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using htlim.const_mul (f 1)
  apply le_of_tendsto_of_tendsto' hleft htf
  intro n
  have htle : t n ≤ 1 := by
    dsimp [t]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hratio := antitoneOn_reaction_div hf hstructure (ht n) (by norm_num) htle
  simpa only [div_one] using (le_div_iff₀ (ht n)).mp hratio

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ s₀ : ℝ}

/-- A negative reaction value gives a strictly negative linear upper bound on the whole tail. -/
theorem Hypotheses.reaction_tail_coercive (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) (hf₀ : f s₀ < 0) :
    0 < -f s₀ / s₀ ∧ ∀ s, s₀ ≤ s → f s ≤ -(-f s₀ / s₀) * s := by
  refine ⟨div_pos (neg_pos.mpr hf₀) hs₀, fun s hs ↦ ?_⟩
  simpa only [neg_div, neg_neg] using
    reaction_le_slope_mul h.reaction_contDiffOn h.reaction_structure hs₀ hs

/-- The same coercive constant controls the excess above the threshold. -/
theorem Hypotheses.reaction_tail_le_neg_excess (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) (hf₀ : f s₀ < 0) {s : ℝ} (hs : s₀ ≤ s) :
    f s ≤ -(-f s₀ / s₀) * (s - s₀) := by
  obtain ⟨hpos, htail⟩ := h.reaction_tail_coercive hs₀ hf₀
  exact (htail s hs).trans (mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr hpos.le))

end SerrinEpigraph
