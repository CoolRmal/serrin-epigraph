module

public import SerrinEpigraph.SharpGlobalLipschitz
public import SerrinEpigraph.SimultaneousMollifiedCompactness
public import SerrinEpigraph.TranslationOrderSet

/-!
# Locally uniform limits of physical translations

A single subsequence converges on every compact set and preserves the sharp
Lipschitz bound and all global translation orders.
-/

public section

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace SerrinEpigraph

/-- Uniformly bounded nonnegative functions with a common Lipschitz constant
admit one locally uniformly convergent subsequence on the whole Euclidean space. -/
theorem exists_locally_uniform_subsequence_of_lipschitz {d : ℕ}
    (F : ℕ → Space d → ℝ) {L : ℝ≥0} {M : ℝ}
    (hL : ∀ j, LipschitzWith L (F j)) (hM : ∀ j x, F j x ∈ Icc 0 M) :
    ∃ (φ : ℕ → ℕ) (V : Space d → ℝ), StrictMono φ ∧ LipschitzWith L V ∧
      (∀ x, V x ∈ Icc 0 M) ∧ ∀ K : Set (Space d), IsCompact K →
        TendstoUniformlyOn (fun j ↦ F (φ j)) V atTop K := by
  let X (k : ℕ) := closedBall (0 : Space d) (k + 1 : ℝ)
  let : ∀ k, CompactSpace (X k) := fun k ↦
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space d) (k + 1 : ℝ))
  let G : ∀ k, ℕ → X k →ᵇ ℝ := fun k j ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ F j x, (hL j).continuous.comp continuous_subtype_val⟩
  obtain ⟨φ, hφ, hv⟩ := exists_simultaneous_uniform_subsequence G (fun _ ↦ L)
    (fun _ ↦ M) (fun k j ↦ (hL j).restrict (X k)) (fun k j x ↦ hM j x)
  choose v hv using hv
  let V (x : Space d) := limUnder atTop (fun j ↦ F (φ j) x)
  have hpoint (x : Space d) : Tendsto (fun j ↦ F (φ j) x) atTop (𝓝 (V x)) := by
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    have hx : x ∈ X k := by simp only [X, mem_closedBall, dist_zero_right]; linarith
    have ht := (hv k).tendsto_at (⟨x, hx⟩ : X k)
    have he : V x = v k ⟨x, hx⟩ := ht.limUnder_eq
    rw [he]
    exact ht
  refine ⟨φ, V, hφ, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hpoint x).dist (hpoint y))
      (Eventually.of_forall (fun j ↦ (hL (φ j)).dist_le_mul x y))
  · intro x
    exact ⟨ge_of_tendsto (hpoint x) (Eventually.of_forall (fun j ↦ (hM (φ j) x).1)),
      le_of_tendsto (hpoint x) (Eventually.of_forall (fun j ↦ (hM (φ j) x).2))⟩
  · intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Space d)
    obtain ⟨k, hk⟩ := exists_nat_gt r
    have hsub : K ⊆ X k := by
      intro x hx
      have hxr : ‖x‖ < r := by simpa using hr hx
      simp only [X, mem_closedBall, dist_zero_right]
      linarith
    apply TendstoUniformlyOn.mono _ hsub
    apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    have he : (fun x : X k ↦ V x) = v k := by
      funext x
      exact ((hv k).tendsto_at x).limUnder_eq
    change TendstoUniformly (fun j (x : X k) ↦ F (φ j) x) (fun x : X k ↦ V x) atTop
    rw [he]
    exact hv k

/-- Physical translates of the original solution have locally uniform limits
which retain every original global translation order. -/
theorem RigidityHypotheses.exists_physical_translation_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (p : ℕ → Space (m + 1)) :
    ∃ (φ : ℕ → ℕ) (V : Space (m + 1) → ℝ), StrictMono φ ∧
      LipschitzWith ⟨κ, h.kappa_pos.le⟩ V ∧ (∀ x, V x ∈ Icc 0 1) ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p (φ j) + x)) V atTop K) ∧
      translationOrderSet (zeroExtension g u) ⊆ translationOrderSet V := by
  have hL (j : ℕ) : LipschitzWith ⟨κ, h.kappa_pos.le⟩
      (fun x ↦ zeroExtension g u (p j + x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left] using (hr.zeroExtension_lipschitzWith h).dist_le_mul
      (p j + x) (p j + y)
  obtain ⟨φ, V, hφ, hV, hbound, hlim⟩ := exists_locally_uniform_subsequence_of_lipschitz
    (fun j x ↦ zeroExtension g u (p j + x)) hL
    (fun j x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
  refine ⟨φ, V, hφ, hV, hbound, hlim, ?_⟩
  apply translationOrderSet_subset_of_translates_tendsto
  intro x
  exact (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)

end SerrinEpigraph
