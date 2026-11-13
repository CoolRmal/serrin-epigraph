module

public import SerrinEpigraph.Boundary
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Connected epigraphs and a positive vertical derivative

Continuous graph domains are path connected. The positive boundary differential also supplies
an interior point with positive vertical derivative, excluding the identically zero alternative
in a strong maximum principle.
-/

@[expose] public section

noncomputable section

namespace SerrinEpigraph

variable {m : ℕ}

/-- A continuous graph domain is the continuous image of an open half-space. -/
theorem isPathConnected_epigraph {g : Space m → ℝ} (hg : Continuous g) :
    IsPathConnected (epigraph g) := by
  let Φ : Space m × ℝ → Space (m + 1) := fun p ↦ point p.1 (g p.1 + p.2)
  have hΦ : Continuous Φ :=
    pointContinuousLinearMap.continuous.comp
      (continuous_fst.prodMk ((hg.comp continuous_fst).add continuous_snd))
  have hconv : Convex ℝ (Set.univ ×ˢ Set.Ioi (0 : ℝ) : Set (Space m × ℝ)) :=
    convex_univ.prod (convex_Ioi 0)
  have hconn := hconv.isPathConnected ⟨(0, 1), by simp⟩
  have himage : Φ '' (Set.univ ×ˢ Set.Ioi (0 : ℝ)) = epigraph g := by
    ext x
    constructor
    · rintro ⟨⟨y, t⟩, ht, rfl⟩
      change g (horizontal (point y (g y + t))) < (point y (g y + t)) (Fin.last m)
      simp only [horizontal_point, last_point]
      exact lt_add_of_pos_right _ ht.2
    · intro hx
      refine ⟨(horizontal x, x (Fin.last m) - g (horizontal x)), ?_, ?_⟩
      · exact ⟨Set.mem_univ _, sub_pos.2 hx⟩
      · change point (horizontal x)
          (g (horizontal x) + (x (Fin.last m) - g (horizontal x))) = x
        convert point_horizontal_last x using 1
        congr 1
        ring
  rw [← himage]
  exact hconn.image hΦ

/-- A continuous graph domain is connected. -/
theorem isConnected_epigraph {g : Space m → ℝ} (hg : Continuous g) :
    IsConnected (epigraph g) :=
  (isPathConnected_epigraph hg).isConnected

/-- Positive Neumann data force a positive interior vertical derivative. -/
theorem exists_verticalDerivative_pos {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ) :
    ∃ x ∈ epigraph g, 0 < verticalDerivative u x := by
  obtain ⟨ε, hε, hpos⟩ := exists_ball_verticalDerivative_pos h (0 : Space m)
  have hboundary := point_mem_closure_epigraph (le_refl (g (0 : Space m)))
  obtain ⟨x, hx, hdist⟩ := Metric.mem_closure_iff.1 hboundary ε hε
  exact ⟨x, hx, hpos x ⟨hx, by simpa only [Metric.mem_ball, dist_comm] using hdist⟩⟩

/-- The vertical derivative cannot vanish throughout the epigraph. -/
theorem not_verticalDerivative_eqOn_zero {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ) :
    ¬ Set.EqOn (verticalDerivative u) (fun _ ↦ 0) (epigraph g) := by
  intro hzero
  obtain ⟨x, hx, hpos⟩ := exists_verticalDerivative_pos h
  exact (ne_of_gt hpos) (hzero hx)

end SerrinEpigraph
