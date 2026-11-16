module

public import SerrinEpigraph.PhysicalTranslationCompactness
public import SerrinEpigraph.LimitEquation

/-!
# The equation retained by a physical translation limit

Uniform convergence on compact sets keeps positive compact subsets inside the
original domains. The equation then passes to the limit with both derivatives
on the compact test function.
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- Strict positivity of a continuous compact limit is uniform and persists
under uniform convergence on that compact set. -/
theorem eventually_positive_on_compact_of_tendstoUniformlyOn {d : ℕ}
    {F : ℕ → Space d → ℝ} {V : Space d → ℝ} {K : Set (Space d)}
    (hK : IsCompact K) (hV : ContinuousOn V K) (hpos : ∀ x ∈ K, 0 < V x)
    (ht : TendstoUniformlyOn F V atTop K) : ∀ᶠ j in atTop, ∀ x ∈ K, 0 < F j x := by
  rcases K.eq_empty_or_nonempty with hK0 | hKn
  · simp [hK0]
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKn hV
  have hε := half_pos (hpos x₀ hx₀)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht (V x₀ / 2) hε] with j hj
  intro x hx
  have hdist := hj x hx
  rw [Real.dist_eq] at hdist
  have hlow := (abs_lt.mp hdist).2
  have hm := hmin hx
  change V x₀ ≤ V x at hm
  linarith

/-- Continuous bounded observables of physical translates converge against
continuous weights on compact sets. -/
theorem RigidityHypotheses.physical_translation_observable_tendsto
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ x, Tendsto (fun j ↦ zeroExtension g u (p j + x)) atTop (𝓝 (V x)))
    {K : Set (Space (m + 1))} (hK : IsCompact K) {ψ : Space (m + 1) → ℝ}
    (hψ : ContinuousOn ψ K) {A : ℝ → ℝ} (hA : ContinuousOn A (Icc 0 1)) :
    Tendsto (fun j ↦ ∫ x in K, A (zeroExtension g u (p j + x)) * ψ x) atTop
      (𝓝 (∫ x in K, A (V x) * ψ x)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hψ
  have hrange (j : ℕ) (x : Space (m + 1)) : zeroExtension g u (p j + x) ∈ Icc 0 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ |C| * |D|)
  · intro j
    have hc : Continuous (fun x ↦ zeroExtension g u (p j + x)) :=
      h.zeroExtension_continuous.comp (continuous_const.add continuous_id)
    exact ((hA.comp hc.continuousOn (fun x _ ↦ hrange j x)).mul hψ).aestronglyMeasurable
      hK.measurableSet
  · exact continuousOn_const.integrableOn_compact hK
  · intro j
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [norm_mul]
    exact mul_le_mul ((hC _ (hrange j x)).trans (le_abs_self C))
      ((hD x hx).trans (le_abs_self D)) (norm_nonneg _) (abs_nonneg _)
  · filter_upwards with x
    have ht : Tendsto (fun j ↦ zeroExtension g u (p j + x)) atTop (𝓝[Icc 0 1] (V x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim x, Eventually.of_forall (fun j ↦ hrange j x)⟩
    exact ((hA _ (hV x)).tendsto.comp ht).mul tendsto_const_nhds

/-- A translated zero extension satisfies the distributional equation whenever
the test support lies in its positive phase. -/
theorem Hypotheses.translated_zeroExtension_distributional_equation
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (p : Space (m + 1)) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ)
    (hs : ∀ x ∈ tsupport φ, 0 < zeroExtension g u (p + x)) :
    (∫ x, zeroExtension g u (p + x) * (Δ φ) x) =
      -∫ x, f (zeroExtension g u (p + x)) * φ x := by
  let Ω := (fun x : Space (m + 1) ↦ x + p) ⁻¹' epigraph g
  have hΩ : IsOpen Ω := (isOpen_epigraph h.graph_contDiff.continuous).preimage
    (continuous_id.add continuous_const)
  have hC : ContDiffOn ℝ 2 (fun x ↦ zeroExtension g u (x + p)) Ω := by
    apply (h.solution_contDiffOn.comp (contDiff_id.add contDiff_const).contDiffOn
      (fun _ hx ↦ hx)).congr
    intro x hx
    exact zeroExtension_of_mem hx
  have hsub : tsupport φ ⊆ Ω := by
    intro x hx
    exact (h.zeroExtension_pos_iff (x + p)).mp (by simpa only [add_comm] using hs x hx)
  have heq := integral_mul_laplacian_eq_neg_source_mul (μ := volume) hΩ hC hφ hc hsub
    (F := fun x ↦ f (zeroExtension g u (x + p))) (fun x hx ↦ by
      rw [laplacian_comp_add_right]
      exact h.zeroExtension_equation ((h.zeroExtension_pos_iff (x + p)).mpr hx))
  simpa only [add_comm] using heq

/-- Every physical translation limit satisfies the original semilinear equation
in distributional form on its actual positive phase. -/
theorem RigidityHypotheses.physical_translation_limit_distributional_equation
    {m : ℕ} {g : Space m → ℝ} {u V φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : Continuous V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {x | 0 < V x}) :
    (∫ x, V x * (Δ φ) x) = -∫ x, f (V x) * φ x := by
  have hpoint (x : Space (m + 1)) :
      Tendsto (fun j ↦ zeroExtension g u (p j + x)) atTop (𝓝 (V x)) :=
    (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hleft := hr.physical_translation_observable_tendsto h hval hpoint hc
    (continuous_laplacian_of_contDiff hφ).continuousOn (A := id) continuousOn_id
  have hright := hr.physical_translation_observable_tendsto h hval hpoint hc
    hφ.continuous.continuousOn (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
  simp only [id_eq, setIntegral_mul_laplacian_test] at hleft
  simp only [setIntegral_mul_test] at hright
  have hpos := eventually_positive_on_compact_of_tendstoUniformlyOn hc hV.continuousOn hs
    (hlim _ hc)
  apply tendsto_nhds_unique hleft
  apply hright.neg.congr'
  filter_upwards [hpos] with j hj
  exact (h.translated_zeroExtension_distributional_equation (p j) hφ hc hj).symm

end SerrinEpigraph
