module

public import SerrinEpigraph.CalibrationVariation
public import SerrinEpigraph.WeakLinearization

/-!
# Differentiating calibrated energy on compact sets
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Filter Metric
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Compactness makes the allowed interval of variation uniform in the spatial point. -/
theorem exists_uniform_level_variation {K : Set (Space (m + 1))} (hK : IsCompact K)
    {v φ : Space (m + 1) → ℝ} (hv : ∀ x ∈ K, ContinuousAt v x)
    (hφ : Continuous φ) (hval : ∀ x ∈ K, v x ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ δ > 0, ∀ t ∈ closedBall (0 : ℝ) δ, ∀ x ∈ K,
      v x + t * φ x ∈ Set.Ioo (0 : ℝ) 1 := by
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ K, v x + t * φ x ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hc : ContinuousAt (fun p : ℝ × Space (m + 1) ↦ v p.2 + p.1 * φ p.2) (0, x) :=
      ((hv x hx).comp continuous_snd.continuousAt).add
        (continuous_fst.continuousAt.mul (hφ.continuousAt.comp continuous_snd.continuousAt))
    exact hc.eventually (isOpen_Ioo.mem_nhds (by simpa using hval x hx))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε / 2, half_pos hε, fun t ht x hx ↦ hsub ?_ x hx⟩
  exact (closedBall_subset_ball (half_lt_self hε)) ht

/-- The foliation gradient is C¹ on the full intermediate-level strip. -/
theorem RigidityHypotheses.levelGradient_contDiffOn_strip (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ContDiffOn ℝ 1 (hr.levelGradient h) {p : Space m × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) 1} :=
  fun _ hp ↦ (hr.levelGradient_contDiffAt h hp).contDiffWithinAt

/-- Calibrated energy can be differentiated under its compact spatial integral. -/
theorem RigidityHypotheses.calibratedDensity_integral_hasDerivAt
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v φ : Space (m + 1) → ℝ} {Ω K : Set (Space (m + 1))}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω) (hφ : ContDiff ℝ 1 φ)
    (hK : IsCompact K) (hsub : K ⊆ Ω) (hval : ∀ x ∈ K, v x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t ↦ ∫ x in K,
      hr.calibratedDensity h (horizontal x) (v x + t * φ x)
        (gradient v x + t • gradient φ x))
      (∫ x in K, inner ℝ (hr.comparisonField h v x) (gradient φ x) +
        (inner ℝ (fderiv ℝ (hr.levelGradient h) (horizontal x, v x) (0, 1))
          (gradient v x - hr.comparisonField h v x) - f (v x)) * φ x) 0 := by
  obtain ⟨δ, hδ, hδval⟩ := exists_uniform_level_variation hK
    (fun x hx ↦ hv.continuousOn.continuousAt (hΩ.mem_nhds (hsub hx))) hφ.continuous hval
  let C := closedBall (0 : ℝ) δ ×ˢ K
  let S := {p : Space m × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) 1}
  let P := fun p : ℝ × Space (m + 1) ↦ (horizontal p.2, v p.2 + p.1 * φ p.2)
  let Z := fun p : ℝ × Space (m + 1) ↦ gradient v p.2 + p.1 • gradient φ p.2
  have hvc : ContinuousOn (fun p : ℝ × Space (m + 1) ↦ v p.2) C :=
    (hv.continuousOn.mono hsub).comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hφc : Continuous (fun p : ℝ × Space (m + 1) ↦ φ p.2) :=
    hφ.continuous.comp continuous_snd
  have hPc : ContinuousOn P C :=
    (continuous_horizontal.comp continuous_snd).continuousOn.prodMk
      (hvc.add (continuous_fst.continuousOn.mul hφc.continuousOn))
  have hmap : Set.MapsTo P C S := fun p hp ↦ hδval p.1 hp.1 p.2 hp.2
  have hgc : ContinuousOn (gradient v) K :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      ((hv.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub)
  have hgφ : Continuous (gradient φ) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hZc : ContinuousOn Z C :=
    (hgc.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)).add
      (continuous_fst.continuousOn.smul (hgφ.comp continuous_snd).continuousOn)
  have hS : IsOpen S := isOpen_Ioo.preimage continuous_snd
  have hBc := (hr.levelGradient_contDiffOn_strip h).continuousOn.comp hPc hmap
  have hDc := ((hr.levelGradient_contDiffOn_strip h).continuousOn_fderiv_of_isOpen hS le_rfl).comp
    hPc hmap
  have hsc : ContinuousOn (fun p : ℝ × Space (m + 1) ↦ v p.2 + p.1 * φ p.2) C :=
    hPc.snd
  have hfc : ContinuousOn (fun p : ℝ × Space (m + 1) ↦ f (v p.2 + p.1 * φ p.2)) C :=
    h.reaction_contDiffOn.continuousOn.comp hsc (fun p hp ↦ (hmap hp).1.le)
  have hW : ContinuousOn (normalizedPotential f) (Set.Ioi (0 : ℝ)) :=
    fun s hs ↦ (h.normalizedPotential_hasDerivAt hs).continuousAt.continuousWithinAt
  have hWc := hW.comp hsc (fun p hp ↦ (hmap hp).1)
  have hF : ContinuousOn
      (fun p : ℝ × Space (m + 1) ↦ hr.calibratedDensity h (horizontal p.2)
        (v p.2 + p.1 * φ p.2) (Z p)) C :=
    ((hBc.inner hZc).sub (hBc.norm.pow 2 |>.div_const 2)).add hWc
  have hF' : ContinuousOn
      (fun p : ℝ × Space (m + 1) ↦ inner ℝ (hr.levelGradient h (P p)) (gradient φ p.2) +
        (inner ℝ (fderiv ℝ (hr.levelGradient h) (P p) (0, 1))
          (Z p - hr.levelGradient h (P p)) - f (P p).2) * φ p.2) C :=
    (hBc.inner (hgφ.comp continuous_snd).continuousOn).add
      (((hDc.clm_apply continuousOn_const).inner (hZc.sub hBc)).sub hfc |>.mul hφc.continuousOn)
  have he := hasDerivAt_setIntegral_of_continuousOn (μ := volume) hK hδ
    (F := fun t x ↦ hr.calibratedDensity h (horizontal x) (v x + t * φ x) (Z (t, x)))
    (F' := fun t x ↦ inner ℝ (hr.levelGradient h (P (t, x))) (gradient φ x) +
      (inner ℝ (fderiv ℝ (hr.levelGradient h) (P (t, x)) (0, 1))
        (Z (t, x) - hr.levelGradient h (P (t, x))) - f (P (t, x)).2) * φ x)
    hF hF' ?_
  · simpa only [Z, P, zero_mul, zero_smul, add_zero, comparisonField] using he
  · intro x hx t ht
    apply hr.calibratedDensity_hasDerivAt h (horizontal x)
    · simpa using ((hasDerivAt_id t).mul_const (φ x)).const_add (v x)
    · change HasDerivAt (fun r ↦ gradient v x + r • gradient φ x) (gradient φ x) t
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id t).smul_const (gradient φ x)).const_add (gradient v x)
    · exact hδval t (ball_subset_closedBall ht) x hx

/-- The calibrated energy integral has derivative zero along each compact variation. -/
theorem RigidityHypotheses.calibratedDensity_integral_hasDerivAt_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v φ : Space (m + 1) → ℝ} {Ω K : Set (Space (m + 1))}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω) (hφ : ContDiff ℝ 1 φ)
    (hK : IsCompact K) (hsub : K ⊆ Ω) (hsupp : tsupport φ ⊆ K)
    (hval : ∀ x ∈ Ω, v x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t ↦ ∫ x in K,
      hr.calibratedDensity h (horizontal x) (v x + t * φ x)
        (gradient v x + t • gradient φ x)) 0 0 := by
  have hd := hr.calibratedDensity_integral_hasDerivAt h hΩ hv hφ hK hsub
    (fun x hx ↦ hval x (hsub hx))
  have hc : HasCompactSupport φ :=
    hK.of_isClosed_subset (isClosed_tsupport φ) hsupp
  have he := hr.calibratedDensity_firstVariation h hΩ hv hval hφ hc (hsupp.trans hsub)
  have hi : (∫ x in K, inner ℝ (hr.comparisonField h v x) (gradient φ x) +
      (inner ℝ (fderiv ℝ (hr.levelGradient h) (horizontal x, v x) (0, 1))
        (gradient v x - hr.comparisonField h v x) - f (v x)) * φ x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact he
    · intro x hx
      have hn : x ∉ tsupport φ := fun ht ↦ hx (hsupp ht)
      have hz : φ x = 0 := Function.notMem_support.mp (fun ht ↦ hn (subset_tsupport φ ht))
      have hg : gradient φ x = 0 := by simp [gradient, fderiv_of_notMem_tsupport ℝ hn]
      simp [hz, hg]
  rwa [hi] at hd

end SerrinEpigraph
