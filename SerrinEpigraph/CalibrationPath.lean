module

public import SerrinEpigraph.CalibrationIntegral
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Constancy of calibrated energy along compact comparison paths
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Gradients vary affinely along a differentiable affine path. -/
theorem gradient_affine_variation {v φ : Space (m + 1) → ℝ} {x : Space (m + 1)}
    (hv : DifferentiableAt ℝ v x) (hφ : DifferentiableAt ℝ φ x) (t : ℝ) :
    gradient (fun y ↦ v y + t * φ y) x = gradient v x + t • gradient φ x := by
  have he : fderiv ℝ (fun y ↦ v y + t * φ y) x =
      fderiv ℝ v x + t • fderiv ℝ φ x := by
    have hd := (hv.hasFDerivAt.add (hφ.hasFDerivAt.const_mul t)).fderiv
    simpa only [Pi.add_def] using hd
  simp only [gradient, he, map_add, map_smul]

/-- At every admissible parameter, the calibrated energy path has derivative zero. -/
theorem RigidityHypotheses.calibratedPath_hasDerivAt_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v φ : Space (m + 1) → ℝ} {Ω K : Set (Space (m + 1))}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω) (hφ : ContDiff ℝ 1 φ)
    (hK : IsCompact K) (hsub : K ⊆ Ω) (hsupp : tsupport φ ⊆ K) {t : ℝ}
    (hval : ∀ x ∈ Ω, v x + t * φ x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r ↦ ∫ x in K,
      hr.calibratedDensity h (horizontal x) (v x + r * φ x)
        (gradient v x + r • gradient φ x)) 0 t := by
  let V := fun x ↦ v x + t * φ x
  have hV : ContDiffOn ℝ 1 V Ω := hv.add (contDiffOn_const.mul hφ.contDiffOn)
  have hd := hr.calibratedDensity_integral_hasDerivAt_zero h hΩ hV hφ hK hsub hsupp hval
  have hg (x : Space (m + 1)) (hx : x ∈ K) :
      gradient V x = gradient v x + t • gradient φ x :=
    gradient_affine_variation
      ((hv.differentiableOn_one x (hsub hx)).differentiableAt (hΩ.mem_nhds (hsub hx)))
      (hφ.differentiable_one x) t
  have hd' : HasDerivAt (fun r ↦ ∫ x in K,
      hr.calibratedDensity h (horizontal x) (V x + r * φ x)
        (gradient V x + r • gradient φ x)) 0 (t - t) := by simpa using hd
  have hc := hd'.comp (h := fun r ↦ r - t) t ((hasDerivAt_id t).sub_const t)
  simp only [zero_mul] at hc
  apply hc.congr_of_eventuallyEq
  filter_upwards with r
  apply setIntegral_congr_fun hK.measurableSet
  intro x hx
  dsimp only
  rw [hg x hx]
  have hs : V x + (r - t) * φ x = v x + r * φ x := by dsimp [V]; ring
  have hz : (gradient v x + t • gradient φ x) + (r - t) • gradient φ x =
      gradient v x + r • gradient φ x := by
    rw [add_assoc, ← add_smul]
    congr 2
    ring
  simp only [hs, hz]

/-- The calibrated energy agrees at both endpoints of an admissible compact affine path. -/
theorem RigidityHypotheses.calibratedPath_endpoints
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v φ : Space (m + 1) → ℝ} {Ω K : Set (Space (m + 1))}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω) (hφ : ContDiff ℝ 1 φ)
    (hK : IsCompact K) (hsub : K ⊆ Ω) (hsupp : tsupport φ ⊆ K)
    (hval : ∀ x ∈ Ω, v x ∈ Set.Ioo (0 : ℝ) 1)
    (hend : ∀ x ∈ Ω, v x + φ x ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ x in K, hr.calibratedDensity h (horizontal x) (v x + φ x)
      (gradient v x + gradient φ x)) =
      ∫ x in K, hr.calibratedDensity h (horizontal x) (v x) (gradient v x) := by
  let A := fun t ↦ ∫ x in K, hr.calibratedDensity h (horizontal x) (v x + t * φ x)
    (gradient v x + t • gradient φ x)
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt A 0 t := by
    intro t ht
    apply hr.calibratedPath_hasDerivAt_zero h hΩ hv hφ hK hsub hsupp
    intro x hx
    have h0 := hval x hx
    have h1 := hend x hx
    have he := (convex_Ioo (𝕜 := ℝ) (0 : ℝ) 1) h0 h1
      (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    convert he using 1
    simp only [smul_eq_mul]
    ring

  have hc : ContinuousOn A (Set.Icc (0 : ℝ) 1) :=
    fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  have he := constant_of_has_deriv_right_zero hc
    (fun t ht ↦ (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) 1 (by simp)
  simpa only [A, one_mul, one_smul, zero_mul, zero_smul, add_zero] using he

/-- The solution minimizes energy against compact C¹ perturbations that stay between zero and one. -/
theorem RigidityHypotheses.energy_minimal_compact (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {φ : Space (m + 1) → ℝ} {K : Set (Space (m + 1))}
    (hφ : ContDiff ℝ 1 φ) (hK : IsCompact K) (hsub : K ⊆ epigraph g)
    (hsupp : tsupport φ ⊆ K)
    (hval : ∀ x ∈ epigraph g, u x + φ x ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ x in K, ‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) ≤
      ∫ x in K, ‖gradient (fun y ↦ u y + φ y) x‖ ^ 2 / 2 +
        normalizedPotential f (u x + φ x) := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hg : ContinuousOn (gradient u) K :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      ((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub)
  have hgφ : Continuous (gradient φ) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hz := hg.add hgφ.continuousOn
  have hs : ContinuousOn (fun x ↦ u x + φ x) K :=
    (hu.continuousOn.mono hsub).add hφ.continuous.continuousOn
  have hW : ContinuousOn (normalizedPotential f) (Set.Ioi (0 : ℝ)) :=
    fun s hs ↦ (h.normalizedPotential_hasDerivAt hs).continuousAt.continuousWithinAt
  have hWc := hW.comp hs (fun x hx ↦ (hval x (hsub hx)).1)
  have hBc : ContinuousOn (fun x ↦ hr.levelGradient h (horizontal x, u x + φ x)) K :=
    (hr.levelGradient_contDiffOn_strip h).continuousOn.comp
      (continuous_horizontal.continuousOn.prodMk hs) (fun x hx ↦ hval x (hsub hx))
  have hCi : IntegrableOn (fun x ↦ hr.calibratedDensity h (horizontal x) (u x + φ x)
      (gradient u x + gradient φ x)) K :=
    (((hBc.inner hz).sub (hBc.norm.pow 2 |>.div_const 2)).add hWc).integrableOn_compact hK
  have hEi : IntegrableOn (fun x ↦ ‖gradient u x + gradient φ x‖ ^ 2 / 2 +
      normalizedPotential f (u x + φ x)) K :=
    ((hz.norm.pow 2 |>.div_const 2).add hWc).integrableOn_compact hK
  have he := hr.calibratedPath_endpoints h hΩ hu hφ hK hsub hsupp
    (fun x hx ↦ ⟨h.positive x hx, hr.solution_lt_one x hx⟩) hval
  calc
    _ = ∫ x in K, hr.calibratedDensity h (horizontal x) (u x) (gradient u x) := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      exact (hr.calibratedDensity_solution h (hsub hx)).symm
    _ = ∫ x in K, hr.calibratedDensity h (horizontal x) (u x + φ x)
        (gradient u x + gradient φ x) := he.symm
    _ ≤ ∫ x in K, ‖gradient u x + gradient φ x‖ ^ 2 / 2 +
        normalizedPotential f (u x + φ x) :=
      integral_mono hCi hEi (fun x ↦ hr.calibratedDensity_le h _ _ _)
    _ = _ := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      have hg' := gradient_affine_variation
        ((hu.differentiableOn_one x (hsub hx)).differentiableAt (hΩ.mem_nhds (hsub hx)))
        (hφ.differentiable_one x) 1
      simpa only [one_mul, one_smul, hg'] using
        congrArg (fun z : Space (m + 1) ↦ ‖z‖ ^ 2 / 2 + normalizedPotential f (u x + φ x))
          hg'.symm

end SerrinEpigraph
