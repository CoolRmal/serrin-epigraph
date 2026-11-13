module

public import SerrinEpigraph.LevelBoundary

/-!
# The solution extended by zero outside its epigraph
-/

public section

noncomputable section

open InnerProductSpace Filter
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The whole-space function associated with the positive solution. -/
@[expose] def zeroExtension (g : Space m → ℝ) (u : Space (m + 1) → ℝ) :
    Space (m + 1) → ℝ := (epigraph g).indicator u

/-- The extension agrees with the solution in the positive domain. -/
theorem zeroExtension_of_mem {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    zeroExtension g u x = u x := Set.indicator_of_mem hx u

/-- The extension vanishes outside the positive domain, including on its boundary. -/
theorem zeroExtension_of_notMem {x : Space (m + 1)} (hx : x ∉ epigraph g) :
    zeroExtension g u x = 0 := Set.indicator_of_notMem hx u

/-- The original Dirichlet condition vanishes on the whole frontier. -/
theorem Hypotheses.solution_zero_frontier (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∈ frontier (epigraph g)) : u x = 0 := by
  have he : g (horizontal x) = x (Fin.last m) := by
    simpa only [frontier_epigraph h.graph_contDiff.continuous, Set.mem_ofPred_eq] using hx
  have hd := h.dirichlet (horizontal x)
  rw [he, point_horizontal_last] at hd
  exact hd

/-- The zero extension is continuous throughout the ambient space. -/
theorem Hypotheses.zeroExtension_continuous (h : Hypotheses g u f κ) :
    Continuous (zeroExtension g u) := by
  exact continuous_indicator (fun x hx ↦ h.solution_zero_frontier hx)
    h.solution_contDiffOn_closure.continuousOn

/-- The zero extension is nonnegative everywhere. -/
theorem Hypotheses.zeroExtension_nonneg (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    0 ≤ zeroExtension g u x := by
  by_cases hx : x ∈ epigraph g
  · rw [zeroExtension_of_mem hx]
    exact (h.positive x hx).le
  · rw [zeroExtension_of_notMem hx]

/-- The positive phase of the zero extension is exactly the prescribed epigraph. -/
theorem Hypotheses.zeroExtension_pos_iff (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    0 < zeroExtension g u x ↔ x ∈ epigraph g := by
  by_cases hx : x ∈ epigraph g
  · simp [zeroExtension_of_mem hx, hx, h.positive x hx]
  · simp [zeroExtension_of_notMem hx, hx]

/-- The nonzero support of the zero extension is the positive phase. -/
theorem Hypotheses.support_zeroExtension (h : Hypotheses g u f κ) :
    Function.support (zeroExtension g u) = epigraph g := by
  ext x
  change zeroExtension g u x ≠ 0 ↔ x ∈ epigraph g
  rw [← h.zeroExtension_pos_iff x]
  exact ⟨fun hn ↦ lt_of_le_of_ne (h.zeroExtension_nonneg x) hn.symm, ne_of_gt⟩

/-- The extended solution stays below one everywhere. -/
theorem RigidityHypotheses.zeroExtension_lt_one (hr : RigidityHypotheses g u f)
    (x : Space (m + 1)) : zeroExtension g u x < 1 := by
  by_cases hx : x ∈ epigraph g
  · rw [zeroExtension_of_mem hx]
    exact hr.solution_lt_one x hx
  · rw [zeroExtension_of_notMem hx]
    norm_num

/-- Interior derivatives of the zero extension agree with those of the original solution. -/
theorem zeroExtension_eventuallyEq {x : Space (m + 1)} (hg : Continuous g)
    (hx : x ∈ epigraph g) : zeroExtension g u =ᶠ[𝓝 x] u := by
  filter_upwards [(isOpen_epigraph hg).mem_nhds hx] with y hy
  exact zeroExtension_of_mem hy

/-- The extension is locally constant zero at every point strictly outside the closed epigraph. -/
theorem zeroExtension_eventuallyEq_zero {x : Space (m + 1)}
    (hx : x ∉ closure (epigraph g)) : zeroExtension g u =ᶠ[𝓝 x] 0 := by
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
  exact zeroExtension_of_notMem (fun hz ↦ hy (subset_closure hz))

/-- The extension has the original gradient at every interior point. -/
theorem Hypotheses.gradient_zeroExtension (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    gradient (zeroExtension g u) x = gradient u x :=
  (zeroExtension_eventuallyEq h.graph_contDiff.continuous hx).gradient_eq

/-- Outside the closed positive phase the gradient of the extension is zero. -/
theorem gradient_zeroExtension_of_notMem_closure {x : Space (m + 1)}
    (hx : x ∉ closure (epigraph g)) : gradient (zeroExtension g u) x = 0 := by
  rw [(zeroExtension_eventuallyEq_zero (u := u) hx).gradient_eq]
  simp [gradient]

/-- Vertical sections of the zero extension are nondecreasing on the whole real line. -/
theorem Hypotheses.zeroExtension_vertical_mono (h : Hypotheses g u f κ) (y : Space m) :
    Monotone (fun t ↦ zeroExtension g u (point y t)) := by
  intro s t hst
  dsimp only
  by_cases hs : g y < s
  · have ht := hs.trans_le hst
    have hxs : point y s ∈ epigraph g := by simpa [epigraph] using hs
    have hxt : point y t ∈ epigraph g := by simpa [epigraph] using ht
    rw [zeroExtension_of_mem hxs, zeroExtension_of_mem hxt]
    exact (h.vertical_section_strictMonoOn y).monotoneOn hs ht hst
  · have hxs : point y s ∉ epigraph g := by simpa [epigraph] using hs
    rw [zeroExtension_of_notMem hxs]
    exact h.zeroExtension_nonneg _

/-- The whole-space vertical sections still converge to the positive equilibrium. -/
theorem RigidityHypotheses.zeroExtension_vertical_tendsto_one
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (y : Space m) :
    Tendsto (fun t ↦ zeroExtension g u (point y t)) atTop (𝓝 1) := by
  apply (hr.vertical_section_tendsto_one h y).congr'
  filter_upwards [eventually_gt_atTop (g y)] with t ht
  symm
  exact zeroExtension_of_mem (by simpa [epigraph] using ht)

/-- The extended function satisfies the original equation in its positive phase. -/
theorem Hypotheses.zeroExtension_equation (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : 0 < zeroExtension g u x) :
    -(Δ (zeroExtension g u)) x = f (zeroExtension g u x) := by
  have hxi := (h.zeroExtension_pos_iff x).mp hx
  rw [(laplacian_congr_nhds
    (zeroExtension_eventuallyEq (u := u) h.graph_contDiff.continuous hxi)).self_of_nhds,
    zeroExtension_of_mem hxi]
  exact h.equation x hxi

end SerrinEpigraph
