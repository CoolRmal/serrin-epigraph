module

public import SerrinEpigraph.LocalLimitCompatibility

/-!
# A global representative of the local primitive limits
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- Compatible representatives on a countable measurable cover glue almost everywhere. -/
theorem exists_ae_gluing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : ℕ → Set X) (hS : ∀ k, MeasurableSet (S k))
    (hcover : ∀ x, ∃ k, x ∈ S k) (V : ℕ → X → ℝ)
    (hcompat : ∀ k l, k ≤ l → V k =ᵐ[μ.restrict (S k)] V l) :
    ∃ v : X → ℝ, ∀ k, v =ᵐ[μ.restrict (S k)] V k := by
  classical
  choose n hn using hcover
  refine ⟨fun x ↦ V (n x) x, fun k ↦ ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ i j, i ≤ j → x ∈ S i → V i x = V j x := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i ≤ j
    · filter_upwards [(ae_restrict_iff' (hS i)).mp (hcompat i j hij)] with x hx
      exact fun _ ↦ hx
    · exact Eventually.of_forall (fun _ h ↦ (hij h).elim)
  apply (ae_restrict_iff' (hS k)).mpr
  filter_upwards [hall] with x hx
  intro hxk
  rcases le_total (n x) k with hnk | hkn
  · exact hx (n x) k hnk (hn x)
  · exact (hx k (n x) hkn hxk).symm

/-- One global function represents the primitive subsequential limit on every integer ball. -/
theorem RigidityHypotheses.phasePrimitive_global_integral_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : Space (m + 1) → ℝ,
      (∀ k : ℕ, IntegrableOn v (closedBall 0 (k + 1 : ℝ))) ∧
      (∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
        ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) - v x‖) atTop (𝓝 0)) := by
  obtain ⟨φ, hφ, V, hV, hlim, hcompat⟩ :=
    hr.phasePrimitive_compatible_local_limits h R hR
  have hcover (x : Space (m + 1)) : ∃ k : ℕ, x ∈ closedBall 0 (k + 1 : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    refine ⟨k, ?_⟩
    simp only [mem_closedBall, dist_zero_right]
    linarith
  obtain ⟨v, hv⟩ := exists_ae_gluing volume
    (fun k : ℕ ↦ closedBall (0 : Space (m + 1)) (k + 1 : ℝ))
    (fun _ ↦ measurableSet_closedBall) hcover V hcompat
  refine ⟨φ, hφ, v, fun k ↦ (hV k).congr (hv k).symm, fun k ↦ ?_⟩
  have heq (j : ℕ) :
      (∫ x in closedBall 0 (k + 1 : ℝ),
        ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) - v x‖) =
      ∫ x in closedBall 0 (k + 1 : ℝ),
        ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) - V k x‖ := by
    apply integral_congr_ae
    filter_upwards [hv k] with x hx
    rw [hx]
  simpa only [heq] using hlim k

end SerrinEpigraph
