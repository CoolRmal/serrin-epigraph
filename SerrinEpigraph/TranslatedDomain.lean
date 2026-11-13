module

public import SerrinEpigraph.VerticalLimit

/-!
# Compact sets under upward translation

Upward translates exhaust the whole ambient space, with a uniform positive lower
bound for the translated solution on every fixed compact set.
-/

public section

noncomputable section

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Upward translation preserves horizontal coordinates and adds to the last coordinate. -/
theorem add_vertical_eq_point (x : Space (m + 1)) (t : ℝ) :
    x + t • verticalDirection m = point (horizontal x) (x (Fin.last m) + t) := by
  simpa only [point_horizontal_last] using
    point_add_vertical (horizontal x) (x (Fin.last m)) t

/-- Every compact set stays inside the epigraph after a sufficiently large upward translation. -/
theorem compact_eventually_in_epigraph (hg : Continuous g)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ x ∈ K, x + t • verticalDirection m ∈ epigraph g := by
  have hc : Continuous (fun x : Space (m + 1) ↦ g (horizontal x) - x (Fin.last m)) := by
    apply (hg.comp continuous_horizontal).sub
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C + 1, ?_⟩
  intro t ht x hx
  have hb := hC x hx
  rw [Real.norm_eq_abs] at hb
  rw [add_vertical_eq_point]
  change g (horizontal (point (horizontal x) (x (Fin.last m) + t))) <
    (point (horizontal x) (x (Fin.last m) + t)) (Fin.last m)
  simp only [horizontal_point, last_point]
  linarith [le_abs_self (g (horizontal x) - x (Fin.last m))]

/-- The solution is nondecreasing under upward translation once both points are interior. -/
theorem Hypotheses.solution_mono_vertical_translate (h : Hypotheses g u f κ)
    (x : Space (m + 1)) {s t : ℝ} (hs : x + s • verticalDirection m ∈ epigraph g)
    (hst : s ≤ t) : u (x + s • verticalDirection m) ≤ u (x + t • verticalDirection m) := by
  rw [add_vertical_eq_point] at hs ⊢
  rw [add_vertical_eq_point]
  have hs' : g (horizontal x) < x (Fin.last m) + s := by simpa [epigraph] using hs
  exact (h.vertical_section_strictMonoOn (horizontal x)).monotoneOn hs'
    (by change g (horizontal x) < x (Fin.last m) + t; linarith) (by linarith)

/-- On any fixed compact set, all sufficiently high translated solutions have a common positive
lower bound. The bound depends on the set, not on the later translation height. -/
theorem Hypotheses.compact_translates_uniformly_positive (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    ∃ T c : ℝ, 0 < c ∧ ∀ t : ℝ, T ≤ t → ∀ x ∈ K,
      x + t • verticalDirection m ∈ epigraph g ∧ c ≤ u (x + t • verticalDirection m) := by
  obtain ⟨T, hT⟩ := compact_eventually_in_epigraph h.graph_contDiff.continuous hK
  have hc : ContinuousOn (fun x ↦ u (x + T • verticalDirection m)) K :=
    h.solution_contDiffOn.continuousOn.comp
      (continuous_id.add continuous_const).continuousOn (hT T le_rfl)
  obtain ⟨c, hcpos, hclower⟩ := hK.exists_forall_le' hc
    (fun x hx ↦ h.positive _ (hT T le_rfl x hx))
  refine ⟨T, c, hcpos, fun t ht x hx ↦ ⟨hT t ht x hx, ?_⟩⟩
  exact (hclower x hx).trans (h.solution_mono_vertical_translate x (hT T le_rfl x hx) ht)

end SerrinEpigraph
