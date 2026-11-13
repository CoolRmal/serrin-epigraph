module

public import SerrinEpigraph.QuotientRegularity
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Algebra.Indicator

/-!
# Compactly supported negative-quotient tests away from the boundary
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace SerrinEpigraph

section Topological

variable {X Y : Type*} [TopologicalSpace X] [Zero Y] {s : Set X} {F : X → Y}

/-- Local vanishing on the inside of the frontier keeps the relative support away from it. -/
theorem closure_inter_support_subset_of_locally_zero_on_frontier
    (hzero : ∀ x ∈ frontier s, ∀ᶠ y in 𝓝 x, y ∈ s → F y = 0) :
    closure (s ∩ Function.support F) ⊆ s := by
  intro x hx
  by_contra hxs
  have hfront : x ∈ frontier s :=
    ⟨closure_mono Set.inter_subset_left hx, fun hi ↦ hxs (interior_subset hi)⟩
  obtain ⟨y, hy, hz⟩ := ((mem_closure_iff_frequently.1 hx).and_eventually (hzero x hfront)).exists
  exact hy.2 (hz hy.1)

/-- A compactly supported function that vanishes locally along the frontier has interior support. -/
theorem isCompact_closure_inter_support_subset_of_locally_zero_on_frontier
    (hF : HasCompactSupport F)
    (hzero : ∀ x ∈ frontier s, ∀ᶠ y in 𝓝 x, y ∈ s → F y = 0) :
    IsCompact (closure (s ∩ Function.support F)) ∧ closure (s ∩ Function.support F) ⊆ s := by
  exact ⟨hF.isCompact.of_isClosed_subset isClosed_closure (closure_mono Set.inter_subset_right),
    closure_inter_support_subset_of_locally_zero_on_frontier hzero⟩

end Topological

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The negative quotient is locally zero within the epigraph at every frontier point. -/
theorem eventually_negativeQuotient_eq_zero_on_epigraph_of_mem_frontier
    (h : Hypotheses g u f κ) {x : Space (m + 1)} (hx : x ∈ frontier (epigraph g)) :
    ∀ᶠ z in 𝓝 x, z ∈ epigraph g → negativeQuotient u z = 0 := by
  have heq : g (horizontal x) = x (Fin.last m) := by
    simpa only [frontier_epigraph h.graph_contDiff.continuous, Set.mem_ofPred_eq] using hx
  obtain ⟨ε, hε, hzero⟩ := exists_ball_negativeQuotient_eq_zero h (horizontal x)
  rw [heq, point_horizontal_last] at hzero
  filter_upwards [Metric.ball_mem_nhds x hε] with z hz hzi
  exact hzero z ⟨subset_closure hzi, hz⟩

/-- Multiplying the negative quotient by a compact cutoff produces compact support inside Ω. -/
theorem compact_interior_support_negativeQuotient_mul (h : Hypotheses g u f κ)
    {χ : Space (m + 1) → ℝ} (hχ : HasCompactSupport χ) :
    IsCompact (closure (epigraph g ∩ Function.support (fun x ↦ negativeQuotient u x * χ x))) ∧
      closure (epigraph g ∩ Function.support (fun x ↦ negativeQuotient u x * χ x)) ⊆ epigraph g := by
  apply isCompact_closure_inter_support_subset_of_locally_zero_on_frontier
    hχ.mul_left
  intro x hx
  filter_upwards [eventually_negativeQuotient_eq_zero_on_epigraph_of_mem_frontier h hx]
    with z hz hzi
  simp only [Pi.mul_apply, hz hzi, zero_mul]

/-- The zero extension of a cutoff negative quotient has compact support contained in Ω. -/
theorem hasCompactSupport_indicator_negativeQuotient_mul (h : Hypotheses g u f κ)
    {χ : Space (m + 1) → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport ((epigraph g).indicator (fun x ↦ negativeQuotient u x * χ x)) ∧
      tsupport ((epigraph g).indicator (fun x ↦ negativeQuotient u x * χ x)) ⊆ epigraph g := by
  simpa only [HasCompactSupport, tsupport, Set.support_indicator] using
    compact_interior_support_negativeQuotient_mul h hχ

/-- The zero extension of a continuous cutoff negative quotient is globally continuous. -/
theorem continuous_indicator_negativeQuotient_mul (h : Hypotheses g u f κ)
    {χ : Space (m + 1) → ℝ} (hχ : Continuous χ) :
    Continuous ((epigraph g).indicator (fun x ↦ negativeQuotient u x * χ x)) := by
  apply continuous_indicator
  · intro x hx
    have hxout : x ∉ epigraph g := by
      exact fun hxi ↦ hx.2 ((isOpen_epigraph h.graph_contDiff.continuous).interior_eq.symm ▸ hxi)
    simp only [negativeQuotient_eq_zero_of_mem_closure_not_mem_epigraph h hx.1 hxout, zero_mul]
  · exact (continuousOn_negativeQuotient_closure h).mul hχ.continuousOn

end SerrinEpigraph
