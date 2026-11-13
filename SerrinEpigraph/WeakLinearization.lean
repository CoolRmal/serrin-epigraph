module

public import SerrinEpigraph.WeakEquation
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Differentiating the weak equation

Compact support permits differentiation of translated weak identities using only two derivatives
of the solution. The analytic input is differentiation under an integral on a compact set.
-/

public section

open MeasureTheory Filter Metric InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Continuous derivatives on a compact parameter cylinder justify differentiating its integral. -/
theorem hasDerivAt_setIntegral_of_continuousOn {K : Set E} (hK : IsCompact K)
    {F F' : ℝ → E → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hF : ContinuousOn (Function.uncurry F) (closedBall 0 δ ×ˢ K))
    (hF' : ContinuousOn (Function.uncurry F') (closedBall 0 δ ×ˢ K))
    (hderiv : ∀ x ∈ K, ∀ t ∈ ball 0 δ, HasDerivAt (fun t ↦ F t x) (F' t x) t) :
    HasDerivAt (fun t ↦ ∫ x in K, F t x ∂μ) (∫ x in K, F' 0 x ∂μ) 0 := by
  have hsection : ∀ t ∈ closedBall 0 δ, ContinuousOn (F t) K := fun t ht ↦
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx ↦ ⟨ht, hx⟩)
  have hsection' : ContinuousOn (F' 0) K :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx ↦ ⟨mem_closedBall_self hδ.le, hx⟩)
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall (0 : ℝ) δ).prod hK).exists_bound_of_continuousOn hF'
  have hfinite : IsFiniteMeasure (μ.restrict K) := ⟨by simp [hK.measure_lt_top]⟩
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict K)
    (bound := fun _ ↦ C) (ball_mem_nhds 0 hδ) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · filter_upwards [ball_mem_nhds 0 hδ] with t ht
    exact ((hsection t (ball_subset_closedBall ht)).integrableOn_compact hK).aestronglyMeasurable
  · exact (hsection 0 (mem_closedBall_self hδ.le)).integrableOn_compact hK
  · exact (hsection'.integrableOn_compact hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx t ht
    exact hC (t, x) ⟨ball_subset_closedBall ht, hx⟩
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx t ht
    exact hderiv x hx t ht

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A compact subset of an open set stays in that set under sufficiently small translations. -/
theorem exists_closedBall_translate_subset {K Ω : Set E} (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hsub : K ⊆ Ω) (e : E) :
    ∃ δ > 0, ∀ t ∈ closedBall (0 : ℝ) δ, ∀ x ∈ K, x + t • e ∈ Ω := by
  obtain ⟨ε, hε, hthick⟩ := hK.exists_cthickening_subset_open hΩ hsub
  refine ⟨ε / (‖e‖ + 1), div_pos hε (by positivity), fun t ht x hx ↦ ?_⟩
  apply hthick (mem_cthickening_of_dist_le (x + t • e) x ε K hx ?_)
  have ht' : |t| ≤ ε / (‖e‖ + 1) := by simpa [Real.dist_eq] using ht
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  calc
    |t| * ‖e‖ ≤ |t| * (‖e‖ + 1) := by gcongr; linarith
    _ ≤ ε := (le_div_iff₀ (by positivity : 0 < ‖e‖ + 1)).mp ht'

omit [FiniteDimensional ℝ E] in
/-- The derivative of a translated coefficient integrated against a continuous compact test. -/
theorem hasDerivAt_integral_translate_mul {F ψ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ Ω) (e : E) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, F (x + t • e) * ψ x ∂μ)
      (∫ x, fderiv ℝ F x e * ψ x ∂μ) 0 := by
  obtain ⟨δ, hδ, hδsub⟩ := exists_closedBall_translate_subset hψc hΩ hsub e
  have hmap : Set.MapsTo (fun p : ℝ × E ↦ p.2 + p.1 • e)
      (closedBall 0 δ ×ˢ tsupport ψ) Ω := fun p hp ↦ hδsub p.1 hp.1 p.2 hp.2
  have hcont : Continuous (fun p : ℝ × E ↦ p.2 + p.1 • e) := by fun_prop
  have hd : ContinuousOn (fderiv ℝ F) Ω := hF.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have h := hasDerivAt_setIntegral_of_continuousOn (μ := μ) hψc hδ
    (F := fun t x ↦ F (x + t • e) * ψ x)
    (F' := fun t x ↦ fderiv ℝ F (x + t • e) e * ψ x)
    ((hF.continuousOn.comp hcont.continuousOn hmap).mul
      (hψ.comp continuous_snd).continuousOn)
    (((hd.comp hcont.continuousOn hmap).clm_apply continuousOn_const).mul
      (hψ.comp continuous_snd).continuousOn) ?_
  · have heq (G : E → ℝ) :
        (∫ x in tsupport ψ, G x * ψ x ∂μ) = ∫ x, G x * ψ x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        simp [Function.notMem_support.mp (fun hx' ↦ hx (subset_tsupport ψ hx'))]
    simpa only [heq, zero_smul, add_zero] using h
  · intro x hx t ht
    have hFx := (hF.differentiableOn_one _
      (hδsub t (ball_subset_closedBall ht) x hx)).differentiableAt
      (hΩ.mem_nhds (hδsub t (ball_subset_closedBall ht) x hx))
    have hshift : HasDerivAt (fun t : ℝ ↦ x + t • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add x
    exact (hFx.hasFDerivAt.comp_hasDerivAt t hshift).mul_const (ψ x)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Translations commute with the native Laplacian. -/
theorem laplacian_comp_add_right (u : E → ℝ) (a x : E) :
    (Δ (fun y ↦ u (y + a))) x = (Δ u) (x + a) := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_add_right]

omit [FiniteDimensional ℝ E] in
private theorem integrable_directional_pair_aux {u φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) (v : E) :
    Integrable (fun x ↦ fderiv ℝ u x v * fderiv ℝ φ x v) μ := by
  have hc := ((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub).clm_apply
    (continuousOn_const (c := v))
  have htest := (hφ.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := v))
  have hsupp : Function.support (fun x ↦ fderiv ℝ u x v * fderiv ℝ φ x v) ⊆ tsupport φ :=
    (Function.support_mul_subset_right _ _).trans
      ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ v))
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    ((hc.mul htest.continuousOn).integrableOn_compact hφc)

private theorem translated_weak_equation_aux {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {u φ F : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (heq : ∀ x ∈ Ω, -(Δ u) x = F x)
    (a : E) (hsub : ∀ x ∈ tsupport φ, x + a ∈ Ω) :
    (∑ i, ∫ x, fderiv ℝ u (x + a) (b i) * fderiv ℝ φ x (b i) ∂μ) =
      ∫ x, F (x + a) * φ x ∂μ := by
  let V := (fun x ↦ x + a) ⁻¹' Ω
  have hV : IsOpen V := hΩ.preimage (continuous_id.add continuous_const)
  have huV : ContDiffOn ℝ 2 (fun x ↦ u (x + a)) V :=
    hu.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hx ↦ hx)
  have hsubV : tsupport φ ⊆ V := hsub
  have h := integral_inner_gradient_eq_source_mul (μ := μ) hV huV hφ hφc hsubV
    (F := fun x ↦ F (x + a)) (fun x hx ↦ by
      rw [laplacian_comp_add_right]
      exact heq _ hx)
  have hint (i : ι) : Integrable
      (fun x ↦ fderiv ℝ u (x + a) (b i) * fderiv ℝ φ x (b i)) μ := by
    simpa only [fderiv_comp_add_right] using integrable_directional_pair_aux (μ := μ) hV
      (huV.of_le (by norm_num)) hφ hφc hsubV (b i)
  simpa only [inner_gradient_eq_sum_fderiv b, fderiv_comp_add_right,
    integral_finsetSum _ (fun i _ ↦ hint i)] using h

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The two directional derivatives commute for a `C²` function on its open domain. -/
theorem fderiv_directional_comm {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) {x : E} (hx : x ∈ Ω) (a b : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ u y a) x b =
      fderiv ℝ (fun y ↦ fderiv ℝ u y b) x a := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have hdx := (hd.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
  have hs := ((hu x hx).contDiffAt (hΩ.mem_nhds hx)).isSymmSndFDerivAt (by norm_num)
  simpa [fderiv_clm_apply hdx (differentiableAt_const a),
    fderiv_clm_apply hdx (differentiableAt_const b)] using hs b a

omit [BorelSpace E] [μ.IsAddHaarMeasure] [FiniteDimensional ℝ E] in
private theorem integral_derivative_pair_comm_aux {u φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hsub : tsupport φ ⊆ Ω) (a b : E) :
    (∫ x, fderiv ℝ (fun y ↦ fderiv ℝ u y a) x b * fderiv ℝ φ x a ∂μ) =
      ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ u y b) x a * fderiv ℝ φ x a ∂μ := by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ω
  · rw [fderiv_directional_comm hΩ hu hx a b]
  · have hzero : fderiv ℝ φ x a = 0 := Function.notMem_support.mp fun hmem ↦
      hx (hsub (tsupport_fderiv_apply_subset ℝ a (subset_tsupport _ hmem)))
    simp [hzero]

/-- Differentiating a classical weak equation requires only two derivatives of its solution. -/
theorem integral_inner_gradient_directional_eq_source_derivative {u φ F : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hF : ContDiffOn ℝ 1 F Ω)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω)
    (heq : ∀ x ∈ Ω, -(Δ u) x = F x) (e : E) :
    (∫ x, inner ℝ (gradient (fun y ↦ fderiv ℝ u y e) x) (gradient φ x) ∂μ) =
      ∫ x, fderiv ℝ F x e * φ x ∂μ := by
  let b := stdOrthonormalBasis ℝ E
  have hd : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have hdu (i) : ContDiffOn ℝ 1 (fun x ↦ fderiv ℝ u x (b i)) Ω :=
    hd.clm_apply contDiffOn_const
  have hleft := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    hasDerivAt_integral_translate_mul (μ := μ) hΩ (hdu i)
      ((hφ.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := b i)))
      (hφc.fderiv_apply ℝ (b i)) ((tsupport_fderiv_apply_subset ℝ (b i)).trans hsub) e
  have hright := hasDerivAt_integral_translate_mul (μ := μ) hΩ hF hφ.continuous hφc hsub e
  obtain ⟨δ, hδ, hδsub⟩ := exists_closedBall_translate_subset hφc hΩ hsub e
  have hevent : (fun t : ℝ ↦ ∑ i, ∫ x,
      fderiv ℝ u (x + t • e) (b i) * fderiv ℝ φ x (b i) ∂μ) =ᶠ[𝓝 0]
      (fun t ↦ ∫ x, F (x + t • e) * φ x ∂μ) := by
    filter_upwards [ball_mem_nhds 0 hδ] with t ht
    exact translated_weak_equation_aux b hΩ hu hφ hφc heq (t • e)
      (hδsub t (ball_subset_closedBall ht))
  have hresult := hleft.unique (hright.congr_of_eventuallyEq hevent)
  rw [← hresult]
  simp_rw [integral_derivative_pair_comm_aux hΩ hu hsub]
  simp_rw [inner_gradient_eq_sum_fderiv b]
  apply integral_finsetSum
  intro i _
  have hv : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y e) Ω := hd.clm_apply contDiffOn_const
  exact integrable_directional_pair_aux hΩ hv hφ hφc hsub (b i)

/-- Every directional derivative of the semilinear solution satisfies the linearized weak PDE. -/
theorem Hypotheses.weak_linearized_equation {m : ℕ} {g : Space m → ℝ}
    {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ epigraph g)
    (e : Space (m + 1)) :
    (∫ x, inner ℝ (gradient (fun y ↦ fderiv ℝ u y e) x) (gradient φ x)) =
      ∫ x, deriv f (u x) * fderiv ℝ u x e * φ x := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hF : ContDiffOn ℝ 1 (fun x ↦ f (u x)) (epigraph g) :=
    h.reaction_contDiffOn.comp hu (fun x hx ↦ (h.positive x hx).le)
  rw [integral_inner_gradient_directional_eq_source_derivative hΩ h.solution_contDiffOn
    hF hφ hφc hsub h.equation e]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ epigraph g
  · have hf := (h.reaction_contDiffOn.differentiableOn_one _ (h.positive x hx).le).differentiableAt
      (Ici_mem_nhds (h.positive x hx))
    have hux := (hu.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
    change fderiv ℝ (f ∘ u) x e * φ x = _
    rw [(hf.hasDerivAt.comp_hasFDerivAt x hux.hasFDerivAt).fderiv]
    simp only [smul_apply, smul_eq_mul]
  · have hzero : φ x = 0 := Function.notMem_support.mp
      (fun hx' ↦ hx (hsub (subset_tsupport φ hx')))
    simp [hzero]

/-- In particular, the vertical derivative satisfies the linearized weak equation. -/
theorem Hypotheses.weak_vertical_equation {m : ℕ} {g : Space m → ℝ}
    {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ epigraph g) :
    (∫ x, inner ℝ (gradient (verticalDerivative u) x) (gradient φ x)) =
      ∫ x, deriv f (u x) * verticalDerivative u x * φ x :=
  h.weak_linearized_equation hφ hφc hsub (verticalDirection m)

end SerrinEpigraph
