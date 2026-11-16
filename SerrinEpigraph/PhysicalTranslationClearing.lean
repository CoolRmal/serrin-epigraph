module

public import SerrinEpigraph.CriticalTranslationContact
public import SerrinEpigraph.PhaseClearingHalfBall

/-!
# Nondegeneracy of critical physical translation limits

The clearing estimate prevents a sequence of positive centers from converging
to the interior of the zero phase. Thus a critical zero contact lies on the
actual limiting free boundary.
-/

public section

noncomputable section

open Set Filter Metric
open scoped Topology

namespace SerrinEpigraph

/-- Positive translation centers cannot converge to a zero-phase interior point. -/
theorem RigidityHypotheses.physical_translation_limit_mem_closure_positive
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : ∀ x, 0 ≤ V x)
    (hpos : ∀ j, 0 < zeroExtension g u (p j))
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K) :
    (0 : Space (m + 1)) ∈ closure {x | 0 < V x} := by
  by_contra hn
  rw [Metric.mem_closure_iff] at hn
  push Not at hn
  obtain ⟨ε, hε, havoid⟩ := hn
  obtain ⟨a, R₀, ha, hR₀, hclear⟩ := hr.exists_phase_clearing_constants h
  let R := min R₀ (ε / 2)
  have hR : 0 < R := lt_min hR₀ (half_pos hε)
  have hRε : R < ε := (min_le_right R₀ (ε / 2)).trans_lt (half_lt_self hε)
  have hz (x : Space (m + 1)) (hx : x ∈ closedBall 0 R) : V x = 0 := by
    have hdist : dist 0 x < ε := by rw [dist_comm]; exact hx.trans_lt hRε
    exact le_antisymm (le_of_not_gt (fun hp ↦ (not_le_of_gt hdist) (havoid x hp))) (hV x)
  obtain ⟨j, hj⟩ := (Metric.tendstoUniformlyOn_iff.mp
    (hlim (closedBall 0 R) (isCompact_closedBall _ _)) (a * R) (mul_pos ha hR)).exists
  have hsmall : ∀ x ∈ ball (p j) R, zeroExtension g u x ≤ a * R := by
    intro x hx
    have hxc : x - p j ∈ closedBall 0 R := by
      have hx' : ‖x - p j‖ < R := by simpa only [mem_ball, dist_eq_norm] using hx
      simpa only [mem_closedBall, dist_zero_right] using hx'.le
    have hdist := hj (x - p j) hxc
    rw [hz _ hxc] at hdist
    have he : p j + (x - p j) = x := by abel
    rw [he, dist_zero_left] at hdist
    exact (le_abs_self _).trans hdist.le
  have hzero := hclear (p j) R hR (min_le_left _ _) hsmall (mem_ball_self (half_pos hR))
  exact (hpos j).ne' hzero

end SerrinEpigraph
