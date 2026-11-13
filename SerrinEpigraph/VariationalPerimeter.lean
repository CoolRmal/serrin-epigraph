module

public import SerrinEpigraph.PhaseVectorTestBound

/-!
# Variational perimeter of the limiting phase

The perimeter is the supremum of absolute divergence pairings over compactly
supported C¹ vector fields of norm at most one. It takes values in the extended
nonnegative reals, so infinite perimeter is not collapsed to a real default.
-/

public section

open MeasureTheory Metric
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Divergence expressed as the derivative trace in an orthonormal basis. -/
@[expose] noncomputable def fieldDivergence {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (F : Space d → Space d) (x : Space d) : ℝ :=
  ∑ i, inner ℝ (b i) (fderiv ℝ F x (b i))

/-- The variational perimeter, tested by compactly supported unit C¹ vector fields. -/
@[expose] noncomputable def variationalPerimeter {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E Ω : Set (Space d)) : ℝ≥0∞ :=
  ⨆ (F : Space d → Space d) (_ : ContDiff ℝ 1 F) (_ : HasCompactSupport F)
    (_ : tsupport F ⊆ Ω) (_ : ∀ x, ‖F x‖ ≤ 1),
    ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x‖

/-- Enlarging the test domain can only increase variational perimeter. -/
theorem variationalPerimeter_mono {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E : Set (Space d))
    {Ω₁ Ω₂ : Set (Space d)} (hΩ : Ω₁ ⊆ Ω₂) :
    variationalPerimeter b E Ω₁ ≤ variationalPerimeter b E Ω₂ := by
  unfold variationalPerimeter
  refine iSup_le (fun F ↦ iSup_le (fun hF ↦ iSup_le (fun hc ↦
    iSup_le (fun hs ↦ iSup_le (fun hb ↦ ?_)))))
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hc
    (le_iSup_of_le (hs.trans hΩ) (le_iSup_of_le hb le_rfl))))

/-- A containing-set divergence bound bounds the variational perimeter in its subsets. -/
theorem variationalPerimeter_le_of_vector_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω K : Set (Space d)}
    (hΩ : Ω ⊆ K) {B : ℝ}
    (hbound : ∀ F : Space d → Space d, ContDiff ℝ 1 F → HasCompactSupport F →
      tsupport F ⊆ K → (∀ x, ‖F x‖ ≤ 1) →
      ‖∫ x in K, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x‖ ≤ B) :
    variationalPerimeter b E Ω ≤ ENNReal.ofReal B := by
  unfold variationalPerimeter
  refine iSup_le (fun F ↦ iSup_le (fun hF ↦ iSup_le (fun hc ↦
    iSup_le (fun hs ↦ iSup_le (fun hb ↦ ?_)))))
  have hsub := hs.trans hΩ
  have he : (∫ x in K, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
      ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : fderiv ℝ F x = 0 := fderiv_of_notMem_tsupport ℝ
      (fun hh ↦ hx (hsub hh))
    simp [fieldDivergence, hz]
  apply ENNReal.ofReal_le_ofReal
  rw [← he]
  exact hbound F hF hc hsub hb

/-- A finite real upper bound on variational perimeter excludes infinite perimeter. -/
theorem variationalPerimeter_ne_top_of_le {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω : Set (Space d)} {B : ℝ}
    (h : variationalPerimeter b E Ω ≤ ENNReal.ofReal B) :
    variationalPerimeter b E Ω ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-- The limiting phase has finite variational perimeter with surface-order ball bounds. -/
theorem RigidityHypotheses.limiting_phase_perimeter_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ → ℝ, (∀ j, 1 ≤ R j) →
      Filter.Tendsto R Filter.atTop Filter.atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
        (∀ k : ℕ, Filter.Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
          ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) -
            E.indicator (fun _ ↦ phasePrimitive f 1) x‖) Filter.atTop (𝓝 0)) ∧
        ∀ (k : ℕ) (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))),
          variationalPerimeter b E (ball 0 (k + 1 : ℝ)) ≤
            ENNReal.ofReal (C * (k + 1 : ℝ) ^ m) := by
  obtain ⟨C, hC, hlim⟩ := hr.limiting_phase_vector_test_bound h
  refine ⟨C, hC, fun R hR hRtop ↦ ?_⟩
  obtain ⟨φ, hφ, E, hE, ht, hb⟩ := hlim R hR hRtop
  refine ⟨φ, hφ, E, hE, ht, fun k b ↦ ?_⟩
  exact variationalPerimeter_le_of_vector_bound b ball_subset_closedBall (hb k b)

end SerrinEpigraph
