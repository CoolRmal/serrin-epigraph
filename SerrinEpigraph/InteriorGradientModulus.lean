module

public import SerrinEpigraph.PlaneTiltPoissonScaling
public import SerrinEpigraph.SharpGlobalLipschitz
public import SerrinEpigraph.ZeroExtension
public import SerrinEpigraph.DistributionalEquation

/-!
# A uniform modulus for the gradient in the positive phase

The interior Poisson gradient estimate `poisson_gradient_sq_le_on_closedBall`, applied to the
translation difference `U(· + w) - U` of the zero extension `U`, gives a modulus of continuity of
`∇U` that is uniform over all centers whose balls of a fixed radius lie in the positive phase.
The forcing-gradient error is controlled by the uniform continuity of the reaction derivative on
`(0, 1]`.

* `RigidityHypotheses.exists_gradient_modulus`: for `r, ε > 0` there is `δ > 0` with
  `‖∇U(Y + w) - ∇U(Y)‖ < ε` whenever `‖w‖ < δ` and `B̄_r(Y)`, `B̄_r(Y + w)` lie in the positive
  phase.
-/

@[expose] public section

noncomputable section

open Set Metric Filter InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The zero extension is `C²` on the open positive phase. -/
theorem Hypotheses.zeroExtension_contDiffOn (h : Hypotheses g u f κ) :
    ContDiffOn ℝ 2 (zeroExtension g u) (epigraph g) :=
  h.solution_contDiffOn.congr fun _ hx ↦ zeroExtension_of_mem hx

/-- A uniform bound and a uniform modulus of continuity for the reaction derivative on
`(0, 1]`. -/
theorem Hypotheses.exists_reaction_deriv_modulus (h : Hypotheses g u f κ) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ s ∈ Ioc (0 : ℝ) 1, |deriv f s| ≤ B) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Ioc (0 : ℝ) 1, ∀ s' ∈ Ioc (0 : ℝ) 1, |s - s'| < δ →
        |deriv f s - deriv f s'| < ε := by
  have hd := h.reaction_contDiffOn.continuousOn_derivWithin (uniqueDiffOn_Ici (0 : ℝ)) le_rfl
  have hd' : ContinuousOn (derivWithin f (Ici 0)) (Icc 0 1) := hd.mono fun _ hs ↦ hs.1
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hd'
  have heq : ∀ s ∈ Ioc (0 : ℝ) 1, derivWithin f (Ici 0) s = deriv f s := fun s hs ↦
    derivWithin_of_mem_nhds (Ici_mem_nhds hs.1)
  refine ⟨max B 0, le_max_right _ _, fun s hs ↦ ?_, fun ε hε ↦ ?_⟩
  · have hb := hB s ⟨hs.1.le, hs.2⟩
    rw [heq s hs, Real.norm_eq_abs] at hb
    exact hb.trans (le_max_left _ _)
  · have huc := isCompact_Icc.uniformContinuousOn_of_continuous hd'
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
    refine ⟨δ, hδ, fun s hs s' hs' hss' ↦ ?_⟩
    have hc := hδ' s ⟨hs.1.le, hs.2⟩ s' ⟨hs'.1.le, hs'.2⟩ (by rwa [Real.dist_eq])
    rwa [Real.dist_eq, heq s hs, heq s' hs'] at hc

/-- The reaction is differentiable at every positive state. -/
theorem Hypotheses.reaction_differentiableAt (h : Hypotheses g u f κ) {s : ℝ} (hs : 0 < s) :
    DifferentiableAt ℝ f s :=
  ((h.reaction_contDiffOn.differentiableOn (by norm_num)) s hs.le).differentiableAt
    (Ici_mem_nhds hs)

/-- The reaction is Lipschitz on `(0, 1]` with any bound for its derivative. -/
theorem Hypotheses.abs_reaction_sub_le (h : Hypotheses g u f κ) {B : ℝ}
    (hB : ∀ s ∈ Ioc (0 : ℝ) 1, |deriv f s| ≤ B) {s s' : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1)
    (hs' : s' ∈ Ioc (0 : ℝ) 1) : |f s - f s'| ≤ B * |s - s'| := by
  have hc := (convex_Ioc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x hx ↦ h.reaction_differentiableAt hx.1) (fun x hx ↦ by
      rw [Real.norm_eq_abs]; exact hB x hx) hs' hs
  simpa only [Real.norm_eq_abs] using hc

/-- The gradient of a translation difference. -/
theorem gradient_translate_sub {d : ℕ} {U : Space d → ℝ} {w Z : Space d}
    (h1 : DifferentiableAt ℝ U (Z + w)) (h2 : DifferentiableAt ℝ U Z) :
    gradient (fun y ↦ U (y + w) - U y) Z = gradient U (Z + w) - gradient U Z := by
  have h1' : DifferentiableAt ℝ (fun y ↦ U (y + w)) Z :=
    h1.comp Z (differentiableAt_id.add_const w)
  simp only [gradient]
  rw [fderiv_fun_sub h1' h2, fderiv_comp_add_right, map_sub]

/-- The derivative of a reaction difference along a vector. -/
theorem Hypotheses.fderiv_reaction_translate_sub_apply (h : Hypotheses g u f κ)
    {U : Space (m + 1) → ℝ} {w Z y : Space (m + 1)} (h1 : DifferentiableAt ℝ U Z)
    (h2 : DifferentiableAt ℝ U (Z + w)) (hU1 : 0 < U Z) (hU2 : 0 < U (Z + w)) :
    fderiv ℝ (fun x ↦ f (U x) - f (U (x + w))) Z y =
      deriv f (U Z) * inner ℝ (gradient U Z) y -
        deriv f (U (Z + w)) * inner ℝ (gradient U (Z + w)) y := by
  have hf1 : HasFDerivAt (fun x ↦ f (U x)) (deriv f (U Z) • fderiv ℝ U Z) Z :=
    (h.reaction_differentiableAt hU1).hasDerivAt.comp_hasFDerivAt Z h1.hasFDerivAt
  have hU' : HasFDerivAt (fun x ↦ U (x + w)) (fderiv ℝ U (Z + w)) Z :=
    (hasFDerivAt_comp_add_right w).mpr h2.hasFDerivAt
  have hf2 : HasFDerivAt (fun x ↦ f (U (x + w))) (deriv f (U (Z + w)) • fderiv ℝ U (Z + w)) Z :=
    (h.reaction_differentiableAt hU2).hasDerivAt.comp_hasFDerivAt Z hU'
  rw [(hf1.fun_sub hf2).fderiv]
  simp only [sub_apply, smul_apply, smul_eq_mul, inner_gradient_left]

/-- The final arithmetic of the gradient modulus. -/
private theorem gradient_modulus_arith {r κ ε K₁ w N : ℝ} (hr0 : 0 < r) (hκ : 0 < κ)
    (hε : 0 < ε) (hK₁ : 0 ≤ K₁) (hw0 : 0 ≤ w)
    (hdiv : N ^ 2 ≤ r ^ 2 * ((ε / (2 * (r * κ + 1)) * κ) ^ 2 / 2) + K₁ * (κ * w) ^ 2)
    (hw : w < ε / (2 * κ * (K₁ + 1))) : N < ε := by
  have hrk : 0 < r * κ + 1 := by positivity
  have hfirst : r ^ 2 * ((ε / (2 * (r * κ + 1)) * κ) ^ 2 / 2) ≤ ε ^ 2 / 8 := by
    have h1 : r ^ 2 * ((ε / (2 * (r * κ + 1)) * κ) ^ 2 / 2) =
        ((r * κ) / (r * κ + 1)) ^ 2 * (ε ^ 2 / 8) := by
      field_simp
      ring
    have h2 : (r * κ) / (r * κ + 1) ≤ 1 := by
      rw [div_le_one hrk]
      linarith
    have h3 : ((r * κ) / (r * κ + 1)) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) h2
    rw [h1]
    calc ((r * κ) / (r * κ + 1)) ^ 2 * (ε ^ 2 / 8) ≤ 1 * (ε ^ 2 / 8) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ε ^ 2 / 8 := one_mul _
  have hsecond : K₁ * (κ * w) ^ 2 ≤ ε ^ 2 / 4 := by
    have h2 : κ * w * (2 * (K₁ + 1)) < ε := by
      rw [lt_div_iff₀ (by positivity)] at hw
      linarith [mul_comm κ w]
    have h4 : (κ * w * (2 * (K₁ + 1))) ^ 2 ≤ ε ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2.le 2
    have h5 : K₁ ≤ (K₁ + 1) ^ 2 := by nlinarith
    have h6 : K₁ * (κ * w) ^ 2 ≤ (K₁ + 1) ^ 2 * (κ * w) ^ 2 :=
      mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
    have h7 : (κ * w * (2 * (K₁ + 1))) ^ 2 = 4 * ((K₁ + 1) ^ 2 * (κ * w) ^ 2) := by ring
    linarith
  have hN2 : N ^ 2 < ε ^ 2 := by
    have : N ^ 2 ≤ ε ^ 2 / 8 + ε ^ 2 / 4 := by linarith
    have hε2 : 0 < ε ^ 2 := by positivity
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hN2

/-- **A uniform modulus for the gradient in the positive phase.** For `r, ε > 0` there is
`δ > 0` such that `‖∇U(Y + w) - ∇U(Y)‖ < ε` whenever `‖w‖ < δ` and both closed balls
`B̄_r(Y)` and `B̄_r(Y + w)` lie in the positive phase. -/
theorem RigidityHypotheses.exists_gradient_modulus (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {r : ℝ} (hr0 : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y w : Space (m + 1), ‖w‖ < δ →
      closedBall Y r ⊆ epigraph g → closedBall (Y + w) r ⊆ epigraph g →
      ‖gradient (zeroExtension g u) (Y + w) - gradient (zeroExtension g u) Y‖ < ε := by
  obtain ⟨B, hB0, hB, hmod⟩ := h.exists_reaction_deriv_modulus
  have hκ := h.kappa_pos
  set U := zeroExtension g u with hUdef
  have hLip := hr.zeroExtension_lipschitzWith h
  have hUlt : ∀ x, U x < 1 := fun x ↦ hr.zeroExtension_lt_one x
  set A : ℝ := r ^ 2 * (B + 1 / 2) + 2 * ((m + 1 : ℕ) : ℝ) + 13 with hA
  have hA0 : 0 ≤ A := by positivity
  set K₁ : ℝ := A * (B + 1 / r ^ 2) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set ε' : ℝ := ε / (2 * (r * κ + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hmod ε' hε'0
  set δ : ℝ := min (δ₁ / κ) (ε / (2 * κ * (K₁ + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ0, fun Y w hw hY hYw ↦ ?_⟩
  have hepi : IsOpen (epigraph g) := isOpen_epigraph h.graph_contDiff.continuous
  set Ω : Set (Space (m + 1)) := {Z | Z ∈ epigraph g ∧ Z + w ∈ epigraph g} with hΩdef
  have hΩ : IsOpen Ω := hepi.inter (hepi.preimage (continuous_id.add continuous_const))
  have hcΩ : closedBall Y r ⊆ Ω := fun Z hZ ↦ ⟨hY hZ, hYw (by
    rw [mem_closedBall] at hZ ⊢
    rwa [dist_add_right])⟩
  have hU2 : ContDiffOn ℝ 2 U (epigraph g) := h.zeroExtension_contDiffOn
  have hU2at : ∀ Z ∈ epigraph g, ContDiffAt ℝ 2 U Z := fun Z hZ ↦
    hU2.contDiffAt (hepi.mem_nhds hZ)
  have hUdiff : ∀ Z ∈ epigraph g, DifferentiableAt ℝ U Z := fun Z hZ ↦
    (hU2at Z hZ).differentiableAt (by norm_num)
  have hUpos : ∀ Z ∈ epigraph g, 0 < U Z := fun Z hZ ↦ (h.zeroExtension_pos_iff Z).mpr hZ
  set v : Space (m + 1) → ℝ := fun Z ↦ U (Z + w) - U Z with hvdef
  set F : Space (m + 1) → ℝ := fun Z ↦ f (U Z) - f (U (Z + w)) with hFdef
  have htr : ∀ Z ∈ Ω, ContDiffAt ℝ 2 (fun y ↦ U (y + w)) Z := fun Z hZ ↦
    (hU2at _ hZ.2).comp Z (contDiff_id.add contDiff_const).contDiffAt
  have hv : ContDiffOn ℝ 2 v Ω := fun Z hZ ↦
    ((htr Z hZ).sub (hU2at Z hZ.1)).contDiffWithinAt
  have hU1Ω : ContDiffOn ℝ 1 U Ω := (hU2.of_le (by norm_num)).mono fun _ hZ ↦ hZ.1
  have hU1Ωw : ContDiffOn ℝ 1 (fun y ↦ U (y + w)) Ω := fun Z hZ ↦
    ((htr Z hZ).of_le (by norm_num)).contDiffWithinAt
  have hF : ContDiffOn ℝ 1 F Ω :=
    (h.reaction_contDiffOn.comp hU1Ω fun Z _ ↦ h.zeroExtension_nonneg Z).sub
      (h.reaction_contDiffOn.comp hU1Ωw fun Z _ ↦ h.zeroExtension_nonneg (Z + w))
  have heq : ∀ Z ∈ Ω, (Δ v) Z = F Z := by
    intro Z hZ
    have hsub : v = (fun y ↦ U (y + w)) - U := rfl
    rw [hsub, (htr Z hZ).laplacian_sub (hU2at Z hZ.1), laplacian_comp_translation]
    have e1 := h.zeroExtension_equation (hUpos _ hZ.2)
    have e2 := h.zeroExtension_equation (hUpos _ hZ.1)
    simp only [hFdef]
    linarith
  have hUval : ∀ Z, U Z ∈ Icc (0 : ℝ) 1 := fun Z ↦ ⟨h.zeroExtension_nonneg Z, (hUlt Z).le⟩
  have hdiffU : ∀ Z, |U (Z + w) - U Z| ≤ κ * ‖w‖ := by
    intro Z
    have hd := hLip.dist_le_mul (Z + w) Z
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at hd
    exact hd
  have hval : ∀ Z ∈ closedBall Y r, |v Z| ≤ κ * ‖w‖ := fun Z _ ↦ hdiffU Z
  have hsrc : ∀ Z ∈ closedBall Y r, |F Z| ≤ B * (κ * ‖w‖) := by
    intro Z hZ
    have hZΩ := hcΩ hZ
    have h1 : U Z ∈ Ioc (0 : ℝ) 1 := ⟨hUpos Z hZΩ.1, (hUlt Z).le⟩
    have h2 : U (Z + w) ∈ Ioc (0 : ℝ) 1 := ⟨hUpos _ hZΩ.2, (hUlt _).le⟩
    have hl := h.abs_reaction_sub_le hB h1 h2
    calc |F Z| = |f (U Z) - f (U (Z + w))| := rfl
      _ ≤ B * |U Z - U (Z + w)| := hl
      _ ≤ B * (κ * ‖w‖) := by
          rw [abs_sub_comm]
          exact mul_le_mul_of_nonneg_left (hdiffU Z) hB0
  have hgradU : ∀ Z, ‖gradient U Z‖ ≤ κ := by
    intro Z
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hLip
  have hκw : κ * ‖w‖ < δ₁ := by
    have h1 : ‖w‖ < δ₁ / κ := hw.trans_le (min_le_left _ _)
    rw [lt_div_iff₀ hκ] at h1
    linarith [mul_comm κ ‖w‖]
  have hforce : ∀ Z ∈ closedBall Y r, -((B + 1 / 2) * ‖gradient v Z‖ ^ 2) - (ε' * κ) ^ 2 / 2 ≤
      inner ℝ (gradient v Z) (gradient F Z) := by
    intro Z hZ
    have hZΩ := hcΩ hZ
    have hgv : gradient v Z = gradient U (Z + w) - gradient U Z :=
      gradient_translate_sub (hUdiff _ hZΩ.2) (hUdiff _ hZΩ.1)
    have hF' := h.fderiv_reaction_translate_sub_apply (y := gradient v Z) (hUdiff _ hZΩ.1)
      (hUdiff _ hZΩ.2) (hUpos _ hZΩ.1) (hUpos _ hZΩ.2)
    have hin : inner ℝ (gradient v Z) (gradient F Z) =
        deriv f (U Z) * inner ℝ (gradient U Z) (gradient v Z) -
          deriv f (U (Z + w)) * inner ℝ (gradient U (Z + w)) (gradient v Z) := by
      rw [real_inner_comm, inner_gradient_left]
      exact hF'
    set a₁ := deriv f (U Z) with ha₁
    set a₂ := deriv f (U (Z + w)) with ha₂
    set G₁ := gradient U Z with hG₁
    set G₂ := gradient U (Z + w) with hG₂
    set V := gradient v Z with hV
    have hsplit : a₁ * inner ℝ G₁ V - a₂ * inner ℝ G₂ V =
        -(a₂ * ‖V‖ ^ 2) + (a₁ - a₂) * inner ℝ G₁ V := by
      have hG₂' : G₂ = V + G₁ := by rw [hgv]; abel
      rw [hG₂', inner_add_left, real_inner_self_eq_norm_sq]
      ring
    have h1 : U Z ∈ Ioc (0 : ℝ) 1 := ⟨hUpos Z hZΩ.1, (hUlt Z).le⟩
    have h2 : U (Z + w) ∈ Ioc (0 : ℝ) 1 := ⟨hUpos _ hZΩ.2, (hUlt _).le⟩
    have ha₂B : |a₂| ≤ B := hB _ h2
    have hdiffa : |a₁ - a₂| ≤ ε' := by
      have hlt : |U Z - U (Z + w)| < δ₁ := by
        rw [abs_sub_comm]
        exact (hdiffU Z).trans_lt hκw
      exact (hδ₁' _ h1 _ h2 hlt).le
    have hG₁κ : ‖G₁‖ ≤ κ := hgradU Z
    have hcs : |inner ℝ G₁ V| ≤ ‖G₁‖ * ‖V‖ := abs_real_inner_le_norm _ _
    have hterm1 : -(B * ‖V‖ ^ 2) ≤ -(a₂ * ‖V‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self a₂ |>.trans ha₂B) (sq_nonneg ‖V‖)
      linarith
    have hterm2 : -(‖V‖ ^ 2 / 2 + (ε' * κ) ^ 2 / 2) ≤ (a₁ - a₂) * inner ℝ G₁ V := by
      have hprod : |(a₁ - a₂) * inner ℝ G₁ V| ≤ ε' * κ * ‖V‖ := by
        rw [abs_mul]
        calc |a₁ - a₂| * |inner ℝ G₁ V| ≤ ε' * (κ * ‖V‖) :=
              mul_le_mul hdiffa (hcs.trans (mul_le_mul_of_nonneg_right hG₁κ (norm_nonneg _)))
                (abs_nonneg _) hε'0.le
          _ = ε' * κ * ‖V‖ := by ring
      have hamgm : ε' * κ * ‖V‖ ≤ ‖V‖ ^ 2 / 2 + (ε' * κ) ^ 2 / 2 := by
        nlinarith [sq_nonneg (‖V‖ - ε' * κ)]
      linarith [neg_abs_le ((a₁ - a₂) * inner ℝ G₁ V)]
    rw [hin, hsplit]
    nlinarith [hterm1, hterm2]
  have hmain := poisson_gradient_sq_le_on_closedBall (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)
    hΩ hv hF heq hr0 hcΩ (by positivity : (0 : ℝ) ≤ B + 1 / 2)
    (by positivity : (0 : ℝ) ≤ (ε' * κ) ^ 2 / 2) (by positivity : (0 : ℝ) ≤ κ * ‖w‖)
    (by positivity : (0 : ℝ) ≤ B * (κ * ‖w‖)) hval hsrc hforce
  have hgvY : gradient v Y = gradient U (Y + w) - gradient U Y :=
    gradient_translate_sub (hUdiff _ (hcΩ (mem_closedBall_self hr0.le)).2)
      (hUdiff _ (hcΩ (mem_closedBall_self hr0.le)).1)
  rw [hgvY] at hmain
  set N := ‖gradient U (Y + w) - gradient U Y‖ with hN
  -- divide the Poisson estimate by `r ²`
  have hr2 : 0 < r ^ 2 := pow_pos hr0 2
  have hdiv : N ^ 2 ≤ r ^ 2 * ((ε' * κ) ^ 2 / 2) + K₁ * (κ * ‖w‖) ^ 2 := by
    have h1 : r ^ 2 * N ^ 2 ≤ r ^ 2 * (r ^ 2 * ((ε' * κ) ^ 2 / 2) + K₁ * (κ * ‖w‖) ^ 2) := by
      have hA' : (r ^ 2 * (B + 1 / 2) + 2 * ((m + 1 : ℕ) : ℝ) + 13) = A := rfl
      rw [hA'] at hmain
      have hexp : r ^ 2 * (r ^ 2 * ((ε' * κ) ^ 2 / 2) + K₁ * (κ * ‖w‖) ^ 2) =
          r ^ 4 * ((ε' * κ) ^ 2 / 2) + A * (κ * ‖w‖) * (r ^ 2 * (B * (κ * ‖w‖))) +
            A * (κ * ‖w‖) ^ 2 := by
        rw [hK₁]
        field_simp
        ring
      rw [hexp]
      exact hmain
    exact le_of_mul_le_mul_left h1 hr2
  exact gradient_modulus_arith hr0 hκ hε hK₁0 (norm_nonneg w) hdiv
    (hw.trans_le (min_le_right _ _))

/-- **Difference quotients and the gradient.** For `r, ε > 0` there is `δ > 0` such that
`|U(Y + h w) - U(Y) - h ⟪∇U(Y), w⟫| ≤ h ε` for unit `w`, `0 < h < δ` and `B̄_{r + h}(Y)` in the
positive phase. -/
theorem RigidityHypotheses.exists_gradient_difference_quotient (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {r : ℝ} (hr0 : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Y w : Space (m + 1)) (t : ℝ), ‖w‖ = 1 → 0 ≤ t → t < δ →
      closedBall Y (r + t) ⊆ epigraph g →
      |zeroExtension g u (Y + t • w) - zeroExtension g u Y -
        t * inner ℝ (gradient (zeroExtension g u) Y) w| ≤ t * ε := by
  obtain ⟨δ, hδ, hmod⟩ := hr.exists_gradient_modulus h hr0 hε
  refine ⟨δ, hδ, fun Y w t hw ht htδ hball ↦ ?_⟩
  set U := zeroExtension g u with hUdef
  have hepi : IsOpen (epigraph g) := isOpen_epigraph h.graph_contDiff.continuous
  have hU2 : ContDiffOn ℝ 2 U (epigraph g) := h.zeroExtension_contDiffOn
  have hseg : ∀ θ ∈ Icc (0 : ℝ) t, closedBall (Y + θ • w) r ⊆ epigraph g := by
    intro θ hθ Z hZ
    apply hball
    rw [mem_closedBall] at hZ ⊢
    calc dist Z Y ≤ dist Z (Y + θ • w) + dist (Y + θ • w) Y := dist_triangle _ _ _
      _ ≤ r + t := by
        rw [dist_self_add_left, norm_smul, hw, mul_one, Real.norm_of_nonneg hθ.1]
        linarith [hθ.2]
  have hmem : ∀ θ ∈ Icc (0 : ℝ) t, Y + θ • w ∈ epigraph g := fun θ hθ ↦
    hseg θ hθ (mem_closedBall_self hr0.le)
  have hderiv : ∀ θ ∈ Icc (0 : ℝ) t, HasDerivWithinAt
      (fun θ ↦ U (Y + θ • w) - θ * inner ℝ (gradient U Y) w)
      (inner ℝ (gradient U (Y + θ • w)) w - inner ℝ (gradient U Y) w) (Icc 0 t) θ := by
    intro θ hθ
    have hdU : DifferentiableAt ℝ U (Y + θ • w) :=
      (hU2.contDiffAt (hepi.mem_nhds (hmem θ hθ))).differentiableAt (by norm_num)
    have hline : HasDerivAt (fun θ : ℝ ↦ Y + θ • w) w θ := by
      simpa using ((hasDerivAt_id θ).smul_const w).const_add Y
    have h1 : HasDerivAt (fun θ ↦ U (Y + θ • w)) (fderiv ℝ U (Y + θ • w) w) θ :=
      hdU.hasFDerivAt.comp_hasDerivAt θ hline
    have h2 : HasDerivAt (fun θ : ℝ ↦ θ * inner ℝ (gradient U Y) w)
        (inner ℝ (gradient U Y) w) θ := by
      simpa using (hasDerivAt_id θ).mul_const (inner ℝ (gradient U Y) w)
    have h3 := (h1.sub h2).hasDerivWithinAt (s := Icc 0 t)
    rw [← inner_gradient_left] at h3
    exact h3
  have hbound : ∀ θ ∈ Ico (0 : ℝ) t,
      ‖inner ℝ (gradient U (Y + θ • w)) w - inner ℝ (gradient U Y) w‖ ≤ ε := by
    intro θ hθ
    rw [← inner_sub_left, Real.norm_eq_abs]
    have hθ' : θ ∈ Icc (0 : ℝ) t := ⟨hθ.1, hθ.2.le⟩
    have hnorm : ‖θ • w‖ < δ := by
      rw [norm_smul, hw, mul_one, Real.norm_of_nonneg hθ.1]
      linarith [hθ.2]
    have hm := hmod Y (θ • w) hnorm
      ((closedBall_subset_closedBall (by linarith)).trans hball) (hseg θ hθ')
    calc |inner ℝ (gradient U (Y + θ • w) - gradient U Y) w|
        ≤ ‖gradient U (Y + θ • w) - gradient U Y‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ ε := by rw [hw, mul_one]; exact hm.le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t ⟨ht, le_rfl⟩
  simp only [zero_smul, add_zero, zero_mul, sub_zero, Real.norm_eq_abs] at hmv
  rw [show t * ε = ε * t by ring, show U (Y + t • w) - U Y - t * inner ℝ (gradient U Y) w =
    U (Y + t • w) - t * inner ℝ (gradient U Y) w - U Y by ring]
  exact hmv

end SerrinEpigraph
