module

public import SerrinEpigraph.QuadraticPenalization
public import SerrinEpigraph.WeakLaplacianCalculus

/-!
# Bounded comparison on unbounded domains near a stable equilibrium

Quadratic penalization excludes a bounded positive function whose weak
Laplacian is bounded below by a positive multiple of the function. No condition
at spatial infinity or smoothness of the domain boundary is needed.
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter Metric
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- A classical equation with a continuous source gives its weak formulation. -/
theorem hasWeakLaplacian_of_contDiffOn_eq {d : ℕ} {Ω : Set (Space d)}
    {v F : Space d → ℝ} (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (heq : ∀ x ∈ Ω, (Δ v) x = F x) : HasWeakLaplacian Ω v F := by
  intro φ hφ hc hs
  rw [hasWeakLaplacian_of_contDiffOn hΩ hv φ hφ hc hs]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ω
  · rw [heq x hx]
  · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh))
    simp only [hz, mul_zero]

/-- Bounded positive solutions of a strict positive-potential weak inequality
cannot occur on an arbitrary open domain with nonpositive boundary values. -/
theorem nonpos_of_bounded_weak_laplacian_ge_mul {d : ℕ} {Ω : Set (Space d)}
    {v F : Space d → ℝ} {c M : ℝ} (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hvc : ContinuousOn v (closure Ω))
    (hF : ContinuousOn F Ω) (heq : HasWeakLaplacian Ω v F)
    (hc : 0 < c) (hbound : ∀ x ∈ closure Ω, v x ≤ M)
    (hboundary : ∀ x ∈ closure Ω, x ∉ Ω → v x ≤ 0)
    (hlower : ∀ x ∈ Ω, 0 < v x → c * v x ≤ F x) :
    ∀ x ∈ closure Ω, v x ≤ 0 := by
  intro x hx
  by_contra hn
  have hxpos : 0 < v x := lt_of_not_ge hn
  have hxΩ : x ∈ Ω := by by_contra hnot; exact hn (hboundary x hx hnot)
  let a := c * v x / (4 * ((d : ℝ) + 1))
  have ha : 0 < a := by dsimp only [a]; positivity
  have hac : 4 * ((d : ℝ) + 1) * a = c * v x := by dsimp only [a]; field_simp
  obtain ⟨y, hy, hxy, _, hmax⟩ := exists_quadratic_penalized_max hΩ hvc hbound
    hboundary hxΩ hxpos ha
  have htest := weak_laplacian_le_at_upper_test hΩ hv hF heq
    (contDiff_quadraticPenalty a x) hy hmax
  rw [laplacian_quadraticPenalty] at htest
  have hl := hlower y hy (hxpos.trans_le hxy)
  have hmul := mul_le_mul_of_nonneg_left hxy hc.le
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- The classical form of bounded comparison on an unbounded domain. -/
theorem nonpos_of_bounded_laplacian_ge_mul {d : ℕ} {Ω : Set (Space d)}
    {v F : Space d → ℝ} {c M : ℝ} (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 2 v Ω) (hvc : ContinuousOn v (closure Ω))
    (hF : ContinuousOn F Ω) (heq : ∀ x ∈ Ω, (Δ v) x = F x)
    (hc : 0 < c) (hbound : ∀ x ∈ closure Ω, v x ≤ M)
    (hboundary : ∀ x ∈ closure Ω, x ∉ Ω → v x ≤ 0)
    (hlower : ∀ x ∈ Ω, 0 < v x → c * v x ≤ F x) :
    ∀ x ∈ closure Ω, v x ≤ 0 :=
  nonpos_of_bounded_weak_laplacian_ge_mul hΩ (hv.of_le (by norm_num)) hvc hF
    (hasWeakLaplacian_of_contDiffOn_eq hΩ hv heq) hc hbound hboundary hlower

end SerrinEpigraph
