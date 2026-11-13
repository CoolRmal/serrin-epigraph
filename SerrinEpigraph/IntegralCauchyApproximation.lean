module

public import SerrinEpigraph.MollificationIntegralError

/-!
# Integral Cauchy criteria from uniform approximations
-/

public section

open MeasureTheory Metric Filter
open scoped Topology BoundedContinuousFunction

namespace SerrinEpigraph

/-- The integral of the absolute difference satisfies the triangle inequality. -/
theorem integral_norm_sub_triangle {d : ℕ} {K : Set (Space d)}
    {a b c : Space d → ℝ} (ha : IntegrableOn a K) (hb : IntegrableOn b K)
    (hc : IntegrableOn c K) :
    (∫ x in K, ‖a x - c x‖) ≤ (∫ x in K, ‖a x - b x‖) + ∫ x in K, ‖b x - c x‖ := by
  have he := integral_mono (ha.sub hc).norm ((ha.sub hb).norm.add (hb.sub hc).norm)
    (fun x ↦ by simpa only [dist_eq_norm, Pi.sub_apply, Pi.add_apply] using dist_triangle (a x) (b x) (c x))
  simp only [Pi.add_apply] at he
  rw [integral_add (ha.sub hb).norm (hb.sub hc).norm] at he
  simpa only [Pi.sub_apply] using he

/-- Uniformly vanishing approximation errors transfer the local integral Cauchy property. -/
theorem integral_cauchy_of_approximations {d : ℕ} {K : Set (Space d)}
    (F : ℕ → Space d → ℝ) (G : ℕ → ℕ → Space d → ℝ) (δ : ℕ → ℝ)
    (hF : ∀ j, IntegrableOn (F j) K) (hG : ∀ n j, IntegrableOn (G n j) K)
    (hδ : Tendsto δ atTop (𝓝 0))
    (herr : ∀ n j, (∫ x in K, ‖F j x - G n j x‖) ≤ δ n)
    (hc : ∀ n ε, 0 < ε → ∃ N, ∀ j ≥ N, ∀ k ≥ N,
      (∫ x in K, ‖G n j x - G n k x‖) < ε) :
    ∀ ε, 0 < ε → ∃ N, ∀ j ≥ N, ∀ k ≥ N, (∫ x in K, ‖F j x - F k x‖) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := (hδ.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  obtain ⟨N, hN⟩ := hc n (ε / 2) (by positivity)
  refine ⟨N, fun j hj k hk ↦ ?_⟩
  have h1 := integral_norm_sub_triangle (hF j) (hG n j) (hF k)
  have h2 := integral_norm_sub_triangle (hG n j) (hG n k) (hF k)
  have he := herr n k
  have hs : (∫ x in K, ‖G n k x - F k x‖) = ∫ x in K, ‖F k x - G n k x‖ := by
    simp_rw [norm_sub_rev (G n k _) (F k _)]
  rw [hs] at h2
  linarith [herr n j, hN j hj k hk]

/-- Uniform convergence on a compact set implies the integral Cauchy property there. -/
theorem integral_cauchy_of_uniform_convergence {d : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) (F : ℕ → Space d → ℝ) (hF : ∀ j, IntegrableOn (F j) K)
    (v : K → ℝ) (ht : TendstoUniformly (fun j (x : K) ↦ F j x) v atTop) :
    ∀ ε, 0 < ε → ∃ N, ∀ j ≥ N, ∀ k ≥ N, (∫ x in K, ‖F j x - F k x‖) < ε := by
  intro ε hε
  let V := volume.real K
  let η := ε / (4 * (V + 1))
  have hV : 0 ≤ V := measureReal_nonneg
  have hη : 0 < η := div_pos hε (by positivity)
  have hev := (Metric.tendstoUniformly_iff.mp ht) η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun j hj k hk ↦ ?_⟩
  have hp : ∀ x ∈ K, ‖F j x - F k x‖ ≤ 2 * η := by
    intro x hx
    have h1 := hN j hj ⟨x, hx⟩
    have h2 := hN k hk ⟨x, hx⟩
    have hh := dist_triangle (F j x) (v ⟨x, hx⟩) (F k x)
    simp only [dist_eq_norm] at h1 h2 hh
    rw [norm_sub_rev (F j x) (v ⟨x, hx⟩)] at hh
    linarith
  have he := setIntegral_mono_on ((hF j).sub (hF k)).norm
    (continuousOn_const.integrableOn_compact (μ := volume) hK) hK.measurableSet hp
  rw [setIntegral_const, smul_eq_mul] at he
  have hηeq : η * (4 * (V + 1)) = ε := by dsimp [η]; field_simp
  change (∫ x in K, ‖F j x - F k x‖) < ε
  change (∫ x in K, ‖F j x - F k x‖) ≤ V * (2 * η) at he
  nlinarith

/-- A common subsequence of dilated primitives is Cauchy in integral norm on every integer ball. -/
theorem RigidityHypotheses.phasePrimitive_integral_cauchy_subsequence
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N, ∀ i ≥ N, ∀ j ≥ N,
        (∫ x in closedBall 0 (k + 1 : ℝ),
          ‖phasePrimitive f (zeroExtension g u (R (φ i) • x)) -
            phasePrimitive f (zeroExtension g u (R (φ j) • x))‖) < ε := by
  obtain ⟨φ, hφ, hlim⟩ := hr.mollifiedPrimitive_simultaneous_subsequence h R
  obtain ⟨C, _, herr⟩ := hr.rescaledPhasePrimitive_mollification_error h
  refine ⟨φ, hφ, fun k ↦ ?_⟩
  let F : ℕ → Space (m + 1) → ℝ :=
    fun j x ↦ phasePrimitive f (zeroExtension g u (R (φ j) • x))
  have hF (j : ℕ) : Continuous (F j) :=
    (hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul (R (φ j)))
  apply integral_cauchy_of_approximations F (fun n j ↦ mollify (F j) n)
    (fun n ↦ (1 / ((n : ℝ) + 1)) * (C * ((k + 1 : ℝ) + 1) ^ m))
    (fun j ↦ (hF j).continuousOn.integrableOn_compact (isCompact_closedBall 0 (k + 1 : ℝ)))
    (fun n j ↦ (mollify_contDiff (hF j) n).continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall 0 (k + 1 : ℝ)))
  · simpa only [zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (C * ((k + 1 : ℝ) + 1) ^ m))
  · intro n j
    have he := herr (R (φ j)) (k + 1 : ℝ) n (hR (φ j)) (by linarith [Nat.cast_nonneg (α := ℝ) k])
    simp_rw [norm_sub_rev (F j _) (mollify (F j) n _)]
    exact he
  · intro n
    obtain ⟨v, hv⟩ := hlim n k
    exact integral_cauchy_of_uniform_convergence (isCompact_closedBall 0 (k + 1 : ℝ))
      (fun j ↦ mollify (F j) n)
      (fun j ↦ (mollify_contDiff (hF j) n).continuous.continuousOn.integrableOn_compact
        (isCompact_closedBall 0 (k + 1 : ℝ))) v hv

end SerrinEpigraph
