module

public import SerrinEpigraph.HarmonicOneDimensionalLimit

/-!
# Quantitative microscopic tangential symmetry

Small tangential energy on a sufficiently large physical ball forces uniform
closeness to the restriction to the normal line on any prescribed smaller ball.
The constants are uniform over every physical translation of the solution.
-/

public section
noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The normal projection onto a unit line does not enlarge the norm. -/
theorem norm_inner_smul_unit_le {d : ℕ} {e : Space d} (he : ‖e‖ = 1) (x : Space d) :
    ‖(inner ℝ e x) • e‖ ≤ ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, he, mul_one]
  simpa only [he, one_mul] using abs_real_inner_le_norm e x

/-- A quantitative compactness consequence of the zero-tilt classification:
on any fixed physical ball, small enough tangential energy on a larger ball
forces uniformly small oscillation in all tangential directions. -/
theorem RigidityHypotheses.exists_tangential_oscillation_constants
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧
      ∀ c : Space (m + 1),
        (∫ x in closedBall 0 R,
          diffuseTiltDensity 1 (fun y ↦ zeroExtension g u (c + y)) e x) ≤ δ →
        ∀ x ∈ closedBall 0 s,
          |zeroExtension g u (c + x) -
            zeroExtension g u (c + (inner ℝ e x) • e)| < ε := by
  by_contra hn
  push Not at hn
  have hbad (j : ℕ) :
      ∃ c : Space (m + 1),
        (∫ x in closedBall 0 (j + 1 : ℝ),
          diffuseTiltDensity 1 (fun y ↦ zeroExtension g u (c + y)) e x) ≤
            1 / (j + 1 : ℝ) ∧
        ∃ x ∈ closedBall 0 s,
          ε ≤ |zeroExtension g u (c + x) -
            zeroExtension g u (c + (inner ℝ e x) • e)| :=
    hn (j + 1 : ℝ) (1 / (j + 1 : ℝ)) (by positivity) (by positivity)
  choose c hc x hx hfailure using hbad
  have hLip (j : ℕ) : LipschitzWith ⟨κ, h.kappa_pos.le⟩
      (fun y ↦ zeroExtension g u (c j + y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_add_left] using (hr.zeroExtension_lipschitzWith h).dist_le_mul
      (c j + y) (c j + z)
  have ht (K : Set (Space (m + 1))) (hK : IsCompact K) :
      Tendsto (fun j ↦ ∫ z in K,
        diffuseTiltDensity 1 (fun y ↦ zeroExtension g u (c j + y)) e z) atTop (𝓝 0) := by
    obtain ⟨r, hKr⟩ := hK.isBounded.subset_closedBall (0 : Space (m + 1))
    have hlarge : ∀ᶠ j : ℕ in atTop, r ≤ j + 1 := by
      exact (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop r)
    apply squeeze_zero' (Eventually.of_forall (fun j ↦
      integral_nonneg (diffuseTiltDensity_nonneg (by norm_num) _ he))) _
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hlarge] with j hj
    apply le_trans _ (hc j)
    apply setIntegral_mono_set
      (integrableOn_diffuseTiltDensity (hLip j).locallyLipschitz
        (isCompact_closedBall 0 (j + 1 : ℝ)) 1 he)
      (Eventually.of_forall (diffuseTiltDensity_nonneg (by norm_num) _ he))
    exact Eventually.of_forall (hKr.trans (closedBall_subset_closedBall hj))
  obtain ⟨φ, V, _, _, _, hlim, _, hprofile⟩ :=
    hr.exists_oneDimensional_physical_translation_limit h c he ht
  have hsmall := Metric.tendstoUniformlyOn_iff.mp
    (hlim (closedBall 0 s) (isCompact_closedBall 0 s)) (ε / 3) (by positivity)
  obtain ⟨j, hj⟩ := hsmall.exists
  have hy : (inner ℝ e (x (φ j))) • e ∈ closedBall 0 s := by
    rw [mem_closedBall, dist_zero_right]
    exact (norm_inner_smul_unit_le he _).trans
      (by simpa only [mem_closedBall, dist_zero_right] using hx (φ j))
  have h₁ := hj (x (φ j)) (hx (φ j))
  have h₂ := hj ((inner ℝ e (x (φ j))) • e) hy
  rw [Real.dist_eq] at h₁ h₂
  rw [hprofile (x (φ j))] at h₁
  have hb := abs_sub_le
    (zeroExtension g u (c (φ j) + x (φ j)))
    (V ((inner ℝ e (x (φ j))) • e))
    (zeroExtension g u (c (φ j) + (inner ℝ e (x (φ j))) • e))
  rw [abs_sub_comm] at h₁
  linarith [hfailure (φ j)]

end SerrinEpigraph
