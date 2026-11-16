module

public import SerrinEpigraph.WeakGradientComparison

/-!
# Strong gradient convergence of physical translation limits

The global boundary inequality controls the gradient difference directly by
the uniform difference of the functions. No interior regularity of the limit
or convergence of its free boundary is assumed.
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- A uniformly convergent family of bounded weak subsolutions has strongly
convergent gradients when tested with a compact nonnegative cutoff. -/
theorem integral_cutoff_gradient_sub_sq_tendsto
    {d : ℕ} {v : ℕ → Space d → ℝ} {w : Space d → ℝ}
    {a : ℕ → Space d → ℝ} {b φ : Space d → ℝ} {L : NNReal} {A : ℝ}
    (hv : ∀ j, LipschitzWith L (v j)) (hw : LipschitzWith L w)
    (ha : ∀ j, Measurable (a j)) (hb : Measurable b)
    (hA : ∀ j x, ‖a j x‖ ≤ A) (hB : ∀ x, ‖b x‖ ≤ A)
    (hweakv : ∀ j ψ, LocallyLipschitz ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) → (∫ x, inner ℝ (gradient (v j) x) (gradient ψ x) - a j x * ψ x) ≤ 0)
    (hweakw : ∀ ψ, LocallyLipschitz ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) → (∫ x, inner ℝ (gradient w x) (gradient ψ x) - b x * ψ x) ≤ 0)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφval : ∀ x, φ x ∈ Icc 0 1)
    (hlim : TendstoUniformlyOn v w atTop (tsupport φ)) :
    Tendsto (fun j ↦ ∫ x in tsupport φ, φ x * ‖gradient (v j) x - gradient w x‖ ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨D, hD⟩ := gradient_bound_of_locallyLipschitz hφ.locallyLipschitz hc
  have hDall (x : Space d) : ‖gradient φ x‖ ≤ D := by
    by_cases hx : x ∈ tsupport φ
    · exact hD x hx
    · simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
  let C := 4 * ((L : ℝ) * D + A) * volume.real (tsupport φ)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hB 0)
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim (ε / (C + 1)) hδ] with j hj
  have hclose (x : Space d) (hx : x ∈ tsupport φ) : |v j x - w x| ≤ ε / (C + 1) := by
    simpa only [Real.dist_eq, abs_sub_comm] using (hj x hx).le
  have hi := integral_gradient_sub_sq_le_of_weak_inequalities (hv j) hw (ha j) hb
    (hA j) hB D.coe_nonneg (hweakv j) hweakw hφ hc hφval hDall hclose
  have hnonneg : 0 ≤ ∫ x in tsupport φ, φ x * ‖gradient (v j) x - gradient w x‖ ^ 2 :=
    integral_nonneg (fun x ↦ mul_nonneg (hφval x).1 (sq_nonneg _))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have hupper : 4 * (ε / (C + 1)) * ((L : ℝ) * D + A) * volume.real (tsupport φ) =
      (ε / (C + 1)) * C := by dsimp only [C]; ring
  rw [hupper] at hi
  apply hi.trans_lt
  have he : (ε / (C + 1)) * (C + 1) = ε := div_mul_cancel₀ ε (by linarith)
  nlinarith

/-- Every physical translate obeys the same weak inequality with compact
Lipschitz tests as its limits. -/
theorem RigidityHypotheses.translated_zeroExtension_lipschitz_test
    {m : ℕ} {g : Space m → ℝ} {u ψ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (p : Space (m + 1)) (hψ : LocallyLipschitz ψ) (hc : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) :
    (∫ x, inner ℝ (gradient (fun y ↦ zeroExtension g u (p + y)) x) (gradient ψ x) -
      f (zeroExtension g u (p + x)) * ψ x) ≤ 0 := by
  have hlip : LipschitzWith ⟨κ, h.kappa_pos.le⟩ (fun x ↦ zeroExtension g u (p + x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left] using (hr.zeroExtension_lipschitzWith h).dist_le_mul (p + x) (p + y)
  exact hr.physical_translation_limit_lipschitz_test h (p := fun _ ↦ p) hlip
    (fun x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
    (fun _ ↦ tendsto_const_nhds) hψ hc hψ0

/-- The actual physical translation limit has strongly convergent gradients
against every compact nonnegative smooth cutoff. -/
theorem RigidityHypotheses.physical_translation_cutoff_gradient_tendsto
    {m : ℕ} {g : Space m → ℝ} {u V φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφval : ∀ x, φ x ∈ Icc 0 1) :
    Tendsto (fun j ↦ ∫ x in tsupport φ,
      φ x * ‖gradient (fun y ↦ zeroExtension g u (p j + y)) x - gradient V x‖ ^ 2)
      atTop (𝓝 0) := by
  have hpoint (x : Space (m + 1)) := (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hreact := h.reaction_contDiffOn.continuousOn
  have hrange (j : ℕ) (x : Space (m + 1)) : zeroExtension g u (p j + x) ∈ Icc 0 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hreact.mono Icc_subset_Ici_self)
  have hlip (j : ℕ) :
      LipschitzWith ⟨κ, h.kappa_pos.le⟩ (fun x ↦ zeroExtension g u (p j + x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left] using
      (hr.zeroExtension_lipschitzWith h).dist_le_mul (p j + x) (p j + y)
  exact integral_cutoff_gradient_sub_sq_tendsto hlip hV
    (fun j ↦ (hreact.comp_continuous (hlip j).continuous (fun x ↦ (hrange j x).1)).measurable)
    (hreact.comp_continuous hV.continuous (fun x ↦ (hval x).1)).measurable
    (fun j x ↦ hA _ (hrange j x)) (fun x ↦ hA _ (hval x))
    (fun j ψ ↦ hr.translated_zeroExtension_lipschitz_test h (p j) (ψ := ψ))
    (fun ψ ↦ hr.physical_translation_limit_lipschitz_test h hV hval hpoint (ψ := ψ))
    hφ hc hφval (hlim _ hc)

/-- Two Lipschitz gradients have an integrable squared difference on compact sets. -/
theorem integrableOn_gradient_sub_sq_of_lipschitz
    {d : ℕ} {v w : Space d → ℝ} {L : NNReal} (hv : LipschitzWith L v)
    (hw : LipschitzWith L w) {K : Set (Space d)} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ ‖gradient v x - gradient w x‖ ^ 2) K := by
  apply (continuousOn_const.integrableOn_compact hK
    (f := fun _ : Space d ↦ (2 * (L : ℝ)) ^ 2)).mono'
    (((measurable_gradient v).sub (measurable_gradient w)).norm.pow_const 2).aestronglyMeasurable
  filter_upwards with x
  change ‖‖gradient v x - gradient w x‖ ^ 2‖ ≤ (2 * (L : ℝ)) ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  have hgv : ‖gradient v x‖ ≤ L := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      norm_fderiv_le_of_lipschitz ℝ hv (x₀ := x)
  have hgw : ‖gradient w x‖ ≤ L := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      norm_fderiv_le_of_lipschitz ℝ hw (x₀ := x)
  exact (norm_sub_le _ _).trans (by linarith)

/-- Physical translation limits converge strongly in the local gradient norm
on every compact set, including sets crossing the limiting free boundary. -/
theorem RigidityHypotheses.physical_translation_gradient_tendsto
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖gradient (zeroExtension g u) (p j + x) - gradient V x‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space (m + 1))
  let φ : ContDiffBump (0 : Space (m + 1)) :=
    { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := by linarith }
  have hone (x : Space (m + 1)) (hx : x ∈ K) : φ x = 1 :=
    φ.one_of_mem_closedBall (ball_subset_closedBall (hKR hx))
  have hKφ : K ⊆ tsupport (φ : Space (m + 1) → ℝ) := by
    intro x hx
    exact subset_tsupport _ (by change φ x ≠ 0; rw [hone x hx]; norm_num)
  have ht := hr.physical_translation_cutoff_gradient_tendsto h hV hval hlim
    φ.contDiff φ.hasCompactSupport (fun x ↦ ⟨φ.nonneg, φ.le_one⟩)
  simp only [gradient, fderiv_comp_add_left] at ht
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ sq_nonneg _)) _ ht
  intro j
  have hlip : LipschitzWith ⟨κ, h.kappa_pos.le⟩
      (fun x ↦ zeroExtension g u (p j + x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left] using
      (hr.zeroExtension_lipschitzWith h).dist_le_mul (p j + x) (p j + y)
  have hi := (integrableOn_gradient_sub_sq_of_lipschitz hlip hV φ.hasCompactSupport).bdd_mul
    φ.continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x ↦ show ‖φ x‖ ≤ (1 : ℝ) by
        rw [Real.norm_of_nonneg φ.nonneg]; exact φ.le_one))
  have he : (∫ x in K, ‖gradient (zeroExtension g u) (p j + x) - gradient V x‖ ^ 2) =
      ∫ x in K, φ x * ‖gradient (fun y ↦ zeroExtension g u (p j + y)) x - gradient V x‖ ^ 2 := by
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    simp only [hone x hx, one_mul, gradient, fderiv_comp_add_left]
  rw [he]
  have hh := setIntegral_mono_set hi
    (Eventually.of_forall (fun x ↦ mul_nonneg φ.nonneg (sq_nonneg _)))
    (Eventually.of_forall hKφ)
  simpa only [gradient, fderiv_comp_add_left] using hh

end SerrinEpigraph
