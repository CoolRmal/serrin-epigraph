module

public import SerrinEpigraph.ExteriorBallSlope
public import SerrinEpigraph.EventualTranslationOrder
public import SerrinEpigraph.UnitShellVolume
public import SerrinEpigraph.GluedCompetitor
public import SerrinEpigraph.ModicaBound
public import SerrinEpigraph.PotentialComparison
public import SerrinEpigraph.StrongMaximum

/-!
# Connectedness of the Positive Phase of Physical Translation Limits

This module formalizes sections DS7 and DS9.2–DS9.3 of
`docs/rigidity-proof/distance-and-sliding.md`:

1. **Uniform surface-order ball energy under arbitrary translations**:
   Translating `radialCutoffCompetitor` shows that `zeroExtension g u (p + ·)` satisfies a uniform
   surface-order energy bound `∫_{closedBall 0 R} e(U(p + ·)) ≤ C * R ^ m` for every center `p`
   and `R ≥ 1`, which passes to every physical translation limit `V`.
2. **Transfer of phase-energy minimality to physical translation limits (DS7)**:
   Gluing `(Z - δ_j)_+` inside `ball 0 (r + 1)` to `U(p_j + ·)` outside `ball 0 (r + 2)` across
   the unit annulus where `Z = V` avoids any spurious zero-phase potential jump and transfers
   unshifted phase-energy minimality to `V`.
3. **Modica logarithmic equilibrium barrier and coarse-cone inheritance (DS7)**:
   Modica's gradient bound `‖∇u‖² / 2 ≤ W(u) ≤ C (1 - u)²` makes `-log (1 - U)` globally
   `√(2 C)`-Lipschitz, keeping `V` uniformly bounded away from `1` at bounded distance from `{V = 0}`
   and preventing `V` from reaching `1` unless `V ≡ 1`. Combining clearing with classical weak
   supersolution barrier comparison transfers `HasUniformBoundaryCoarseCone g e` to `frontier {0 < V}`.
4. **Connectedness of `{x | 0 < V x}` and strict interior translation order (DS7, DS9.2–DS9.3)**:
   The union of positive coarse cones from `frontier {0 < V}` is preconnected and contains every
   point of `{0 < V}` at distance `> 4 * R_cone` from `{V = 0}`. Any additional open clopen piece
   of `{0 < V}` would lie within distance `4 * R_cone` of `{V = 0}` (hence `V ≤ b_* < 1` there),
   forcing exponential ball-energy growth under iterative cutoff erasure and contradicting the
   surface-order bound. On the connected positive phase `{0 < V}`, annular barrier propagation
   yields `0 < V y → V y < V (y + a₀)` and forces critical contacts to occur at `V 0 = V a₀ = 0`.
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology NNReal Laplacian

namespace SerrinEpigraph

/-- Local Lipschitz multiplication on `Space d`, avoiding the `PiLp` vs `WithLp` diamond. -/
private theorem locallyLipschitz_mul_real {d : ℕ} {f g : Space d → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x ↦ f x * g x) :=
  (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦ z.1 * z.2)).locallyLipschitz.comp (hf.prodMk hg)

/-- Positive part of a `LocallyLipschitz` function on `Space d`. -/
private theorem locallyLipschitz_posPart_real {d : ℕ} {f : Space d → ℝ}
    (hf : LocallyLipschitz f) : LocallyLipschitz (fun x ↦ max (f x) 0) :=
  hf.max ((contDiff_const (c := (0 : ℝ)) : ContDiff ℝ 1 (fun _ : Space d ↦ (0 : ℝ))).locallyLipschitz)

/-- Nonnegativity of unshifted `phaseEnergyDensity` when `normalizedPotential` is nonnegative on `[0, 1]`. -/
private theorem phaseEnergyDensity_nonneg_zero {d : ℕ} {f : ℝ → ℝ} {v : Space d → ℝ}
    (hW : ∀ {s : ℝ}, s ∈ Icc (0 : ℝ) 1 → 0 ≤ normalizedPotential f s)
    (hv : ∀ x, v x ∈ Icc (0 : ℝ) 1) (x : Space d) :
    0 ≤ phaseEnergyDensity f 0 v x := by
  rw [phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hv y).1) f x]
  refine add_nonneg (by positivity) ?_
  by_cases hp : 0 < v x
  · rw [indicator_of_mem (s := {y | 0 < v y}) hp]
    exact hW (hv x)
  · rw [indicator_of_notMem (s := {y | 0 < v y}) hp]

/-- Uniform unit-shell energy bound for arbitrary translates of `zeroExtension g u`. -/
theorem RigidityHypotheses.translated_phaseEnergy_le_unitShell
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ M : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hM : 0 ≤ M) (hW : ∀ s ∈ Icc (0 : ℝ) 1, normalizedPotential f s ≤ M)
    (p : Space (m + 1)) (R : ℝ) :
    (∫ x in closedBall 0 R,
      phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (p + y)) x) ≤
      ∫ _x in closedBall (0 : Space (m + 1)) (R + 1) \ closedBall 0 R, (1 / 2 + M) := by
  let U := zeroExtension g u
  let Up : Space (m + 1) → ℝ := fun y ↦ U (p + y)
  let Vp : Space (m + 1) → ℝ := radialCutoffCompetitor Up R
  let v_unshifted : Space (m + 1) → ℝ := fun z ↦ Vp (-p + z)
  let B := closedBall (0 : Space (m + 1)) R
  let A := closedBall (0 : Space (m + 1)) (R + 1)
  have hAB : B ⊆ A := closedBall_subset_closedBall (by linarith)
  have hUp_lip : LocallyLipschitz Up :=
    h.zeroExtension_locallyLipschitz.comp (isometry_add_left p).lipschitzWith.locallyLipschitz
  have hUp_val (y : Space (m + 1)) : Up y ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hVp_lip : LocallyLipschitz Vp := radialCutoffCompetitor_locallyLipschitz hUp_lip R
  have hv_lip : LocallyLipschitz v_unshifted :=
    hVp_lip.comp (isometry_add_left (-p)).lipschitzWith.locallyLipschitz
  have hv_val (z : Space (m + 1)) : v_unshifted z ∈ Icc (0 : ℝ) 1 :=
    radialCutoffCompetitor_mem_Icc hUp_val R (-p + z)
  have hv_supp : tsupport (fun z ↦ v_unshifted z - U z) ⊆ closedBall p (R + 1) := by
    apply closure_minimal _ isClosed_closedBall
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hnorm : R + 1 < ‖-p + z‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hnot
      have heq : -p + z = z - p := by abel
      rwa [heq]
    have heq_v : Vp (-p + z) = Up (-p + z) :=
      radialCutoffCompetitor_eq (fun y ↦ (hUp_val y).2) hnorm.le
    have hpz : p + (-p + z) = z := by abel
    exact hz (sub_eq_zero.mpr (by dsimp only [v_unshifted]; rw [heq_v]; dsimp only [Up]; rw [hpz]))
  have hm_unshifted := hr.phaseEnergy_minimal_lipschitz_closedRange h hv_lip
    (isCompact_closedBall p (R + 1)) hv_supp hv_val
  have hpre : (fun x ↦ p + x) ⁻¹' closedBall p (R + 1) = A := by
    ext x
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, A]
    have heq : p + x - p = x - 0 := by abel
    rw [heq]
  have hchg1 : (∫ z in closedBall p (R + 1), phaseEnergyDensity f 0 U z) =
      ∫ x in A, phaseEnergyDensity f 0 Up x := by
    have hi := integral_add_left_eq_self (μ := volume)
      (fun z ↦ (closedBall p (R + 1)).indicator (phaseEnergyDensity f 0 U) z) p
    rw [integral_indicator isClosed_closedBall.measurableSet] at hi
    have hcongr : (fun x ↦ (closedBall p (R + 1)).indicator (phaseEnergyDensity f 0 U) (p + x)) =
        A.indicator (phaseEnergyDensity f 0 Up) := by
      funext x
      by_cases hx : x ∈ A
      · have hpx : p + x ∈ closedBall p (R + 1) := by rwa [← mem_preimage, hpre]
        rw [indicator_of_mem hpx, indicator_of_mem hx, phaseEnergyDensity_comp_add_left]
      · have hpx : p + x ∉ closedBall p (R + 1) := by rwa [← mem_preimage, hpre]
        rw [indicator_of_notMem hpx, indicator_of_notMem hx]
    rw [hcongr, integral_indicator isClosed_closedBall.measurableSet] at hi
    exact hi.symm
  have hchg2 : (∫ z in closedBall p (R + 1), phaseEnergyDensity f 0 v_unshifted z) =
      ∫ x in A, phaseEnergyDensity f 0 Vp x := by
    have hi := integral_add_left_eq_self (μ := volume)
      (fun z ↦ (closedBall p (R + 1)).indicator (phaseEnergyDensity f 0 v_unshifted) z) p
    rw [integral_indicator isClosed_closedBall.measurableSet] at hi
    have hv_eq : (fun y ↦ v_unshifted (p + y)) = Vp := by
      funext y; dsimp only [v_unshifted]; congr 1; abel
    have hcongr : (fun x ↦ (closedBall p (R + 1)).indicator
          (phaseEnergyDensity f 0 v_unshifted) (p + x)) =
        A.indicator (phaseEnergyDensity f 0 Vp) := by
      funext x
      by_cases hx : x ∈ A
      · have hpx : p + x ∈ closedBall p (R + 1) := by rwa [← mem_preimage, hpre]
        rw [indicator_of_mem hpx, indicator_of_mem hx,
          ← phaseEnergyDensity_comp_add_left, hv_eq]
      · have hpx : p + x ∉ closedBall p (R + 1) := by rwa [← mem_preimage, hpre]
        rw [indicator_of_notMem hpx, indicator_of_notMem hx]
    rw [hcongr, integral_indicator isClosed_closedBall.measurableSet] at hi
    exact hi.symm
  rw [hchg1, hchg2] at hm_unshifted
  have hiE : IntegrableOn (phaseEnergyDensity f 0 Up) A :=
    h.integrableOn_lipschitz_phaseEnergy hUp_lip hUp_val 0 (isCompact_closedBall _ _)
  have hiF : IntegrableOn (phaseEnergyDensity f 0 Vp) A :=
    h.integrableOn_lipschitz_phaseEnergy hVp_lip
      (radialCutoffCompetitor_mem_Icc hUp_val R) 0 (isCompact_closedBall _ _)
  have hiC : IntegrableOn (fun _ : Space (m + 1) ↦ (1 / 2 + M)) (A \ B) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _)).mono_set sdiff_subset
  have hz : (∫ x in B, phaseEnergyDensity f 0 Vp x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hv0 : Vp x = 0 := radialCutoffCompetitor_zero (fun y ↦ (hUp_val y).1) hx
    simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hv0,
      lt_self_iff_false, ite_false]
  have hB : MeasurableSet B := isClosed_closedBall.measurableSet
  have he := integral_inter_add_sdiff hB hiE
  have hf := integral_inter_add_sdiff hB hiF
  rw [inter_eq_right.mpr hAB] at he hf
  rw [hz, zero_add] at hf
  have hae_Up : ∀ᵐ x, DifferentiableAt ℝ Up x :=
    ae_differentiableAt_of_locallyLipschitz hUp_lip
  have hshell : (∫ x in A \ B, phaseEnergyDensity f 0 Vp x) ≤
      (∫ x in A \ B, phaseEnergyDensity f 0 Up x) + ∫ _x in A \ B, (1 / 2 + M) := by
    rw [← integral_add (hiE.mono_set sdiff_subset) hiC]
    apply integral_mono_ae (hiF.mono_set sdiff_subset) ((hiE.mono_set sdiff_subset).add hiC)
    filter_upwards [ae_restrict_of_ae hae_Up] with x hx
    exact hr.radialCutoff_phaseEnergy_le h hM hW hUp_lip.continuous hUp_val hx R
  linarith

/-- Every physical translation limit satisfies the uniform surface-order ball-energy bound
`∫_{closedBall 0 R} phaseEnergyDensity f 0 V ≤ C * R ^ m` for all `R ≥ 1`. -/
theorem RigidityHypotheses.physical_translation_limit_surface_growth
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      (∫ x in closedBall 0 R, phaseEnergyDensity f 0 V x) ≤ C * R ^ m := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    h.normalizedPotential_continuousOn
  have hW : ∀ s ∈ Icc (0 : ℝ) 1, normalizedPotential f s ≤ |M| :=
    fun s hs ↦ (le_abs_self _).trans ((hM s hs).trans (le_abs_self M))
  let C₀ : ℝ := 1 / 2 + |M|
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  let D : ℝ := volume.real (closedBall (0 : Space (m + 1)) 1) * (m + 1 : ℝ) * 2 ^ m
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg measureReal_nonneg (by positivity)) (by positivity)
  refine ⟨C₀ * (D + 1), mul_pos hC₀ (by linarith), fun R hR ↦ ?_⟩
  let K := closedBall (0 : Space (m + 1)) R
  have hK : IsCompact K := isCompact_closedBall _ _
  have ht_norm := hr.physical_translation_energy_tendsto h hV hval hlim hK
  have ht_int : Tendsto (fun j ↦ ∫ x in K,
      phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (p j + y)) x) atTop
      (𝓝 (∫ x in K, phaseEnergyDensity f 0 V x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ ht_norm
    intro j
    have hUj : LocallyLipschitz (fun y ↦ zeroExtension g u (p j + y)) :=
      h.zeroExtension_locallyLipschitz.comp
        (isometry_add_left (p j)).lipschitzWith.locallyLipschitz
    have hUval (y : Space (m + 1)) : zeroExtension g u (p j + y) ∈ Icc 0 1 :=
      ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
    have hi1 := h.integrableOn_lipschitz_phaseEnergy hUj hUval 0 hK
    have hi2 := h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hval 0 hK
    rw [← integral_sub hi1 hi2]
    exact norm_integral_le_integral_norm _
  apply le_of_tendsto ht_int
  refine Eventually.of_forall (fun j ↦ ?_)
  have hshell := hr.translated_phaseEnergy_le_unitShell h (abs_nonneg M) hW (p j) R
  rw [setIntegral_const, smul_eq_mul, mul_comm] at hshell
  have hs := mul_le_mul_of_nonneg_left (real_volume_unitShell_le m hR) hC₀.le
  have hp : 0 ≤ R ^ m := pow_nonneg (by linarith) _
  calc
    (∫ x in K, phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (p j + y)) x)
      ≤ C₀ * volume.real (closedBall (0 : Space (m + 1)) (R + 1) \ closedBall 0 R) := hshell
    _ ≤ C₀ * (D * R ^ m) := hs
    _ ≤ (C₀ * (D + 1)) * R ^ m := by nlinarith

/-- **Transfer of phase-energy minimality to physical translation limits (DS7)**:
Every physical translation limit `V` minimizes unshifted phase energy against every locally
Lipschitz competitor `Z` valued in `[0, 1]` with `tsupport (Z - V) ⊆ closedBall 0 r` (`0 ≤ r`). -/
theorem RigidityHypotheses.physical_translation_limit_energy_minimal
    {m : ℕ} {g : Space m → ℝ} {u V Z : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ r : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hr_nn : 0 ≤ r)
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hV_val : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hZ : LocallyLipschitz Z) (hZ_val : ∀ x, Z x ∈ Icc 0 1)
    (hsupp : tsupport (fun x ↦ Z x - V x) ⊆ closedBall 0 r) :
    (∫ x in closedBall 0 (r + 2), phaseEnergyDensity f 0 V x) ≤
      ∫ x in closedBall 0 (r + 2), phaseEnergyDensity f 0 Z x := by
  let U := zeroExtension g u
  let Useq : ℕ → Space (m + 1) → ℝ := fun j x ↦ U (p j + x)
  let K_out := closedBall (0 : Space (m + 1)) (r + 2)
  let B_in := ball (0 : Space (m + 1)) (r + 1)
  let A_ann := K_out \ B_in
  have hK_out : IsCompact K_out := isCompact_closedBall _ _
  have hK_ne : K_out.Nonempty := nonempty_closedBall.mpr (by linarith)
  have hB_sub : B_in ⊆ K_out :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hB_meas : MeasurableSet B_in := isOpen_ball.measurableSet
  have hA_comp : IsCompact A_ann := hK_out.diff isOpen_ball
  have hZV_eq {x : Space (m + 1)} (hx : r < ‖x‖) : Z x = V x := by
    have hnot : x ∉ Function.support (fun y ↦ Z y - V y) := by
      intro hm
      have hcb := hsupp (subset_tsupport _ hm)
      rw [mem_closedBall, dist_zero_right] at hcb
      linarith
    exact sub_eq_zero.mp (Function.notMem_support.mp hnot)
  let η : ContDiffBump (0 : Space (m + 1)) :=
    { rIn := r + 1
      rOut := r + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hη_lip : LocallyLipschitz (η : Space (m + 1) → ℝ) :=
    (η.contDiff (n := 1)).locallyLipschitz
  have hη_val (x : Space (m + 1)) : (η : Space (m + 1) → ℝ) x ∈ Icc 0 1 :=
    ⟨η.nonneg, η.le_one⟩
  have hη_supp : tsupport (η : Space (m + 1) → ℝ) ⊆ K_out := by
    rw [η.tsupport_eq]
  obtain ⟨Cη, hCη⟩ := gradient_bound_of_locallyLipschitz hη_lip hK_out
  let δ_seq : ℕ → ℝ := fun j ↦
    sSup ((fun x ↦ |Useq j x - V x|) '' K_out) + 1 / ((j : ℝ) + 1)
  have hδ_pos (j : ℕ) : 0 < δ_seq j := by
    obtain ⟨x₀, hx₀⟩ := hK_ne
    have hbdd : BddAbove ((fun x ↦ |Useq j x - V x|) '' K_out) :=
      (hK_out.image (((h.zeroExtension_continuous.comp
        (continuous_const.add continuous_id)).sub hV.continuous).abs)).bddAbove
    have h0 : 0 ≤ sSup ((fun x ↦ |Useq j x - V x|) '' K_out) :=
      (abs_nonneg _).trans (le_csSup hbdd ⟨x₀, hx₀, rfl⟩)
    have hinv : 0 < 1 / ((j : ℝ) + 1) := by positivity
    dsimp only [δ_seq]
    linarith
  have hδ_ge (j : ℕ) {x : Space (m + 1)} (hx : x ∈ K_out) :
      |Useq j x - V x| < δ_seq j := by
    have hbdd : BddAbove ((fun y ↦ |Useq j y - V y|) '' K_out) :=
      (hK_out.image (((h.zeroExtension_continuous.comp
        (continuous_const.add continuous_id)).sub hV.continuous).abs)).bddAbove
    have hle : |Useq j x - V x| ≤ sSup ((fun y ↦ |Useq j y - V y|) '' K_out) :=
      le_csSup hbdd ⟨x, hx, rfl⟩
    have hinv : 0 < 1 / ((j : ℝ) + 1) := by positivity
    dsimp only [δ_seq]
    linarith
  have hδ_lim : Tendsto δ_seq atTop (𝓝 0) := by
    have hsup_lim : Tendsto (fun j ↦ sSup ((fun x ↦ |Useq j x - V x|) '' K_out)) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hlim K_out hK_out) (ε / 2)
        (half_pos hε)] with j hj
      obtain ⟨x₀, hx₀⟩ := hK_ne
      have hbdd : BddAbove ((fun y ↦ |Useq j y - V y|) '' K_out) :=
        (hK_out.image (((h.zeroExtension_continuous.comp
          (continuous_const.add continuous_id)).sub hV.continuous).abs)).bddAbove
      have h0 : 0 ≤ sSup ((fun y ↦ |Useq j y - V y|) '' K_out) :=
        (abs_nonneg _).trans (le_csSup hbdd ⟨x₀, hx₀, rfl⟩)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
      have hle : sSup ((fun y ↦ |Useq j y - V y|) '' K_out) ≤ ε / 2 := by
        refine csSup_le ⟨|Useq j x₀ - V x₀|, ⟨x₀, hx₀, rfl⟩⟩ ?_
        rintro _ ⟨y, hy, rfl⟩
        have hd := hj y hy
        rw [Real.dist_eq, abs_sub_comm] at hd
        exact hd.le
      linarith
    simpa only [add_zero] using hsup_lim.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let vj : ℕ → Space (m + 1) → ℝ := fun j x ↦ max (Z x - δ_seq j) 0
  let Wj : ℕ → Space (m + 1) → ℝ := fun j ↦ gluedCompetitor (Useq j) (vj j) η
  have hvj_lip (j : ℕ) : LocallyLipschitz (vj j) := by
    have hsub : LocallyLipschitz (fun x ↦ Z x - δ_seq j) :=
      hZ.sub ((contDiff_const (c := δ_seq j) : ContDiff ℝ 1 _).locallyLipschitz)
    exact locallyLipschitz_posPart_real hsub
  have hvj_val (j : ℕ) (x : Space (m + 1)) : vj j x ∈ Icc 0 1 := by
    refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
    linarith [(hZ_val x).2, hδ_pos j]
  have hUseq_lip (j : ℕ) : LocallyLipschitz (Useq j) :=
    h.zeroExtension_locallyLipschitz.comp
      ((by fun_prop : ContDiff ℝ 1 (fun x : Space (m + 1) ↦ p j + x)).locallyLipschitz)
  have hUseq_val (j : ℕ) (x : Space (m + 1)) : Useq j x ∈ Icc 0 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hWj_lip (j : ℕ) : LocallyLipschitz (Wj j) :=
    gluedCompetitor_locallyLipschitz (hUseq_lip j) (hvj_lip j) hη_lip
  have hWj_val (j : ℕ) (x : Space (m + 1)) : Wj j x ∈ Icc 0 1 :=
    gluedCompetitor_mem_Icc (hUseq_val j) (hvj_val j) hη_val x
  have hmin_j (j : ℕ) :
      (∫ x in K_out, phaseEnergyDensity f 0 (Useq j) x) ≤
        ∫ x in K_out, phaseEnergyDensity f 0 (Wj j) x := by
    let w_unshifted : Space (m + 1) → ℝ := fun z ↦ Wj j (-p j + z)
    have hw_lip : LocallyLipschitz w_unshifted :=
      (hWj_lip j).comp (isometry_add_left (-p j)).lipschitzWith.locallyLipschitz
    have hw_val (z : Space (m + 1)) : w_unshifted z ∈ Icc 0 1 := hWj_val j (-p j + z)
    have hw_supp : tsupport (fun z ↦ w_unshifted z - U z) ⊆ closedBall (p j) (r + 2) := by
      apply closure_minimal _ isClosed_closedBall
      intro z hz
      rw [Function.mem_support] at hz
      by_contra hnot
      have hnot_K : -p j + z ∉ K_out := by
        rw [mem_closedBall, dist_eq_norm] at hnot
        rw [mem_closedBall, dist_zero_right]
        have heq : -p j + z = z - p j := by abel
        rwa [heq]
      have hη0 : (η : Space (m + 1) → ℝ) (-p j + z) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hm ↦ hnot_K (hη_supp hm))
      have heq_w : Wj j (-p j + z) = Useq j (-p j + z) :=
        gluedCompetitor_eq_reference _ _ _ hη0
      have hpz : p j + (-p j + z) = z := by abel
      exact hz (sub_eq_zero.mpr
        (by dsimp only [w_unshifted]; rw [heq_w]; dsimp only [Useq]; rw [hpz]))
    have hm := hr.phaseEnergy_minimal_lipschitz_closedRange h hw_lip
      (isCompact_closedBall (p j) (r + 2)) hw_supp hw_val
    have hpre : (fun x ↦ p j + x) ⁻¹' closedBall (p j) (r + 2) = K_out := by
      ext x
      simp only [mem_preimage, mem_closedBall, dist_eq_norm, K_out]
      have heq : p j + x - p j = x - 0 := by abel
      rw [heq]
    have hchg (G : Space (m + 1) → ℝ) :
        (∫ z in closedBall (p j) (r + 2), phaseEnergyDensity f 0 (fun z ↦ G (-p j + z)) z) =
          ∫ x in K_out, phaseEnergyDensity f 0 G x := by
      have hi := integral_add_left_eq_self (μ := volume)
        (fun z ↦ (closedBall (p j) (r + 2)).indicator
          (phaseEnergyDensity f 0 (fun z ↦ G (-p j + z))) z) (p j)
      rw [integral_indicator isClosed_closedBall.measurableSet] at hi
      have hG_eq : (fun y ↦ G (-p j + (p j + y))) = G := by funext y; congr 1; abel
      have hcongr : (fun x ↦ (closedBall (p j) (r + 2)).indicator
            (phaseEnergyDensity f 0 (fun z ↦ G (-p j + z))) (p j + x)) =
          K_out.indicator (phaseEnergyDensity f 0 G) := by
        funext x
        by_cases hx : x ∈ K_out
        · have hpx : p j + x ∈ closedBall (p j) (r + 2) := by rwa [← mem_preimage, hpre]
          rw [indicator_of_mem hpx, indicator_of_mem hx,
            ← phaseEnergyDensity_comp_add_left, hG_eq]
        · have hpx : p j + x ∉ closedBall (p j) (r + 2) := by rwa [← mem_preimage, hpre]
          rw [indicator_of_notMem hpx, indicator_of_notMem hx]
      rw [hcongr, integral_indicator isClosed_closedBall.measurableSet] at hi
      exact hi.symm
    have hU_eq : zeroExtension g u = fun z ↦ Useq j (-p j + z) := by
      funext z; dsimp only [Useq, U]; congr 1; abel
    rw [hU_eq, hchg (Useq j), hchg (Wj j)] at hm
    exact hm
  -- Prove `∫_{K_out} e(V) ≤ ∫_{K_out} e(Z) + ε` for every `ε > 0`
  apply le_of_forall_pos_le_add
  intro ε hε
  have hsplit_int (G : Space (m + 1) → ℝ) (hi : IntegrableOn G K_out) :
      (∫ x in K_out, G x) = (∫ x in B_in, G x) + ∫ x in A_ann, G x := by
    have he := integral_inter_add_sdiff hB_meas hi
    rw [inter_eq_right.mpr hB_sub] at he
    exact he.symm
  have ht_Useq : Tendsto (fun j ↦ ∫ x in K_out, phaseEnergyDensity f 0 (Useq j) x) atTop
      (𝓝 (∫ x in K_out, phaseEnergyDensity f 0 V x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _
      (hr.physical_translation_energy_tendsto h hV hV_val hlim hK_out)
    intro j
    have hi1 := h.integrableOn_lipschitz_phaseEnergy (hUseq_lip j) (hUseq_val j) 0 hK_out
    have hi2 := h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hV_val 0 hK_out
    rw [← integral_sub hi1 hi2]
    exact norm_integral_le_integral_norm _
  obtain ⟨MW, hMW⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    h.normalizedPotential_continuousOn
  let P_pot : (Space (m + 1) → ℝ) → Space (m + 1) → ℝ :=
    fun w x ↦ {y | 0 < w y}.indicator (fun y ↦ normalizedPotential f (w y)) x
  have hiP_on (w : Space (m + 1) → ℝ) (hw : Continuous w) (hw_val : ∀ x, w x ∈ Icc 0 1)
      {S : Set (Space (m + 1))} (hS : S ⊆ K_out) : IntegrableOn (P_pot w) S :=
    (((h.normalizedPotential_continuousOn.comp_continuous hw
      hw_val).continuousOn.integrableOn_compact hK_out).indicator
      (isOpen_lt continuous_const hw).measurableSet).mono_set hS
  -- 1. Inner ball `B_in`: `∫_{B_in} e(Wj j) ≤ ∫_{B_in} e(Z) + ε / 4` eventually
  have ht_Bin_pot : Tendsto (fun j ↦ ∫ x in B_in, P_pot (vj j) x) atTop
      (𝓝 (∫ x in B_in, P_pot Z x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ |MW|)
    · intro j
      exact (hiP_on (vj j) (hvj_lip j).continuous (hvj_val j) hB_sub).aestronglyMeasurable
    · exact (continuousOn_const.integrableOn_compact hK_out).mono_set hB_sub
    · intro j
      filter_upwards with x
      dsimp only [P_pot]
      by_cases hp : 0 < vj j x
      · rw [indicator_of_mem (s := {y | 0 < vj j y}) hp]
        exact (hMW _ (hvj_val j x)).trans (le_abs_self MW)
      · rw [indicator_of_notMem (s := {y | 0 < vj j y}) hp, norm_zero]
        exact abs_nonneg MW
    · refine Eventually.of_forall (fun x ↦ ?_)
      dsimp only [P_pot]
      by_cases hp : 0 < Z x
      · rw [indicator_of_mem (s := {y | 0 < Z y}) hp]
        have hev_pos : ∀ᶠ j in atTop, δ_seq j < Z x := hδ_lim.eventually (gt_mem_nhds hp)
        have hsub_t : Tendsto (fun j ↦ Z x - δ_seq j) atTop (𝓝 (Z x)) := by
          simpa only [sub_zero] using (tendsto_const_nhds (x := Z x)).sub hδ_lim
        have hcomp_t : Tendsto (fun j ↦ normalizedPotential f (vj j x)) atTop
            (𝓝 (normalizedPotential f (Z x))) := by
          have hvj_t : Tendsto (fun j ↦ vj j x) atTop (𝓝[Icc 0 1] (Z x)) := by
            refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall (fun j ↦ hvj_val j x)⟩
            exact hsub_t.congr' (hev_pos.mono (fun j hj ↦ (max_eq_left (sub_pos.mpr hj).le).symm))
          exact (h.normalizedPotential_continuousOn (Z x) (hZ_val x)).tendsto.comp hvj_t
        exact hcomp_t.congr' (hev_pos.mono (fun j hj ↦ by
          dsimp only
          have hpj : 0 < vj j x := lt_max_of_lt_left (sub_pos.mpr hj)
          rw [indicator_of_mem (s := {y | 0 < vj j y}) hpj]))
      · have hZ0 : Z x = 0 := le_antisymm (not_lt.mp hp) (hZ_val x).1
        rw [indicator_of_notMem (s := {y | 0 < Z y}) hp]
        refine tendsto_const_nhds.congr' (Eventually.of_forall (fun j ↦ ?_))
        dsimp only
        have hvj0 : vj j x = 0 := by
          dsimp only [vj]
          rw [hZ0, zero_sub]
          exact max_eq_right (neg_nonpos.mpr (hδ_pos j).le)
        have hnpj : ¬ 0 < vj j x := by rw [hvj0]; exact lt_irrefl 0
        rw [indicator_of_notMem (s := {y | 0 < vj j y}) hnpj]
  have hBin_grad_le (j : ℕ) : ∀ᵐ x, ‖gradient (vj j) x‖ ≤ ‖gradient Z x‖ := by
    filter_upwards [ae_differentiableAt_of_locallyLipschitz hZ] with x _
    by_cases hgt : δ_seq j < Z x
    · have hev : vj j =ᶠ[𝓝 x] fun y ↦ Z y - δ_seq j := by
        filter_upwards [(isOpen_lt continuous_const hZ.continuous).mem_nhds hgt] with y hy
        exact max_eq_left (sub_pos.mpr hy).le
      rw [hev.gradient_eq]
      simp only [gradient, fderiv_sub_const]
      exact le_rfl
    · have hvj0 : vj j x = 0 := max_eq_right (sub_nonpos.mpr (not_lt.mp hgt))
      rw [gradient_eq_zero_of_nonneg_zero (fun y ↦ (hvj_val j y).1) hvj0, norm_zero]
      exact norm_nonneg _
  have hev_Bin : ∀ᶠ j in atTop,
      (∫ x in B_in, phaseEnergyDensity f 0 (Wj j) x) ≤
        (∫ x in B_in, phaseEnergyDensity f 0 Z x) + ε / 4 := by
    filter_upwards [ht_Bin_pot.eventually
      (Iio_mem_nhds (by linarith : (∫ x in B_in, P_pot Z x) <
        (∫ x in B_in, P_pot Z x) + ε / 4))] with j hj_pot
    have heq_Bin : Set.EqOn (phaseEnergyDensity f 0 (Wj j)) (phaseEnergyDensity f 0 (vj j)) B_in := by
      intro x hx
      have hev : Wj j =ᶠ[𝓝 x] vj j := by
        filter_upwards [isOpen_ball.mem_nhds hx] with y hy
        exact gluedCompetitor_eq_candidate _ _ _ (η.one_of_mem_closedBall (ball_subset_closedBall hy))
      rw [phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hWj_val j y).1),
        phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hvj_val j y).1), hev.gradient_eq]
      have hxy : Wj j x = vj j x := hev.eq_of_nhds
      by_cases hp : 0 < vj j x
      · have hpW : 0 < Wj j x := by rwa [hxy]
        rw [indicator_of_mem (s := {y | 0 < Wj j y}) hpW,
          indicator_of_mem (s := {y | 0 < vj j y}) hp, hxy]
      · have hpW : ¬ 0 < Wj j x := by rwa [hxy]
        rw [indicator_of_notMem (s := {y | 0 < Wj j y}) hpW,
          indicator_of_notMem (s := {y | 0 < vj j y}) hp]
    rw [setIntegral_congr_fun hB_meas heq_Bin]
    have hi_kvj : IntegrableOn (fun x ↦ ‖gradient (vj j) x‖ ^ 2 / 2) B_in :=
      ((integrableOn_gradient_sq_of_locallyLipschitz (hvj_lip j) hK_out).mono_set hB_sub).div_const 2
    have hi_kZ : IntegrableOn (fun x ↦ ‖gradient Z x‖ ^ 2 / 2) B_in :=
      ((integrableOn_gradient_sq_of_locallyLipschitz hZ hK_out).mono_set hB_sub).div_const 2
    have hsplit_vj : (∫ x in B_in, phaseEnergyDensity f 0 (vj j) x) =
        (∫ x in B_in, ‖gradient (vj j) x‖ ^ 2 / 2) + ∫ x in B_in, P_pot (vj j) x := by
      have hc : Set.EqOn (phaseEnergyDensity f 0 (vj j))
          (fun x ↦ ‖gradient (vj j) x‖ ^ 2 / 2 + P_pot (vj j) x) B_in :=
        fun x _ ↦ phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hvj_val j y).1) f x
      rw [setIntegral_congr_fun hB_meas hc, integral_add hi_kvj
        (hiP_on (vj j) (hvj_lip j).continuous (hvj_val j) hB_sub)]
    have hsplit_Z : (∫ x in B_in, phaseEnergyDensity f 0 Z x) =
        (∫ x in B_in, ‖gradient Z x‖ ^ 2 / 2) + ∫ x in B_in, P_pot Z x := by
      have hc : Set.EqOn (phaseEnergyDensity f 0 Z)
          (fun x ↦ ‖gradient Z x‖ ^ 2 / 2 + P_pot Z x) B_in :=
        fun x _ ↦ phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hZ_val y).1) f x
      rw [setIntegral_congr_fun hB_meas hc, integral_add hi_kZ
        (hiP_on Z hZ.continuous hZ_val hB_sub)]
    have hkin_le : (∫ x in B_in, ‖gradient (vj j) x‖ ^ 2 / 2) ≤
        ∫ x in B_in, ‖gradient Z x‖ ^ 2 / 2 := by
      apply integral_mono_ae hi_kvj hi_kZ
      filter_upwards [ae_restrict_of_ae (hBin_grad_le j)] with x hx
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx 2) (by norm_num)
    rw [hsplit_vj, hsplit_Z]
    have hj_lt : (∫ x in B_in, P_pot (vj j) x) < (∫ x in B_in, P_pot Z x) + ε / 4 := hj_pot
    linarith
  -- 2. Annulus `A_ann`: `Z = V` on an open neighborhood of `A_ann`
  have hAZ_eq : (∫ x in A_ann, phaseEnergyDensity f 0 V x) =
      ∫ x in A_ann, phaseEnergyDensity f 0 Z x := by
    apply setIntegral_congr_fun (isClosed_closedBall.measurableSet.diff hB_meas)
    intro x hx
    have hnx : r + 1 ≤ ‖x‖ := by
      have hnotb : x ∉ B_in := hx.2
      simpa only [B_in, mem_ball, dist_zero_right, not_lt] using hnotb
    have hopen_out : IsOpen {y : Space (m + 1) | r + 1 / 2 < ‖y‖} :=
      isOpen_lt continuous_const continuous_norm
    have hev : V =ᶠ[𝓝 x] Z := by
      filter_upwards [hopen_out.mem_nhds (by linarith : r + 1 / 2 < ‖x‖)] with y hy
      exact (hZV_eq (by linarith : r < ‖y‖)).symm
    have hxy : V x = Z x := hev.eq_of_nhds
    rw [phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hV_val y).1),
      phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hZ_val y).1), hev.gradient_eq]
    by_cases hp : 0 < Z x
    · have hpV : 0 < V x := by rwa [hxy]
      rw [indicator_of_mem (s := {y | 0 < V y}) hpV,
        indicator_of_mem (s := {y | 0 < Z y}) hp, hxy]
    · have hpV : ¬ 0 < V x := by rwa [hxy]
      rw [indicator_of_notMem (s := {y | 0 < V y}) hpV,
        indicator_of_notMem (s := {y | 0 < Z y}) hp]
  -- Potential bound on `A_ann` via uniform continuity of `normalizedPotential f` on `[0, 1]`
  let vol_A : ℝ := volume.real A_ann + 1
  have hvol_A_pos : 0 < vol_A := by
    dsimp only [vol_A]
    linarith [measureReal_nonneg (μ := volume) (s := A_ann)]
  obtain ⟨δ_uc, hδ_uc_pos, huc⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous
      h.normalizedPotential_continuousOn) (ε / (8 * vol_A)) (div_pos hε (by positivity))
  have ht_A_potU : Tendsto (fun j ↦ ∫ x in A_ann, P_pot (Useq j) x) atTop
      (𝓝 (∫ x in A_ann, P_pot V x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _
      (hr.physical_translation_phase_observable_tendsto h hV hV_val hlim
        h.normalizedPotential_continuousOn hA_comp)
    intro j
    have hi1 := hiP_on (Useq j) (hUseq_lip j).continuous (hUseq_val j) (S := A_ann) sdiff_subset
    have hi2 := hiP_on V hV.continuous hV_val (S := A_ann) sdiff_subset
    rw [← integral_sub hi1 hi2]
    exact norm_integral_le_integral_norm _
  have hev_A_pot : ∀ᶠ j in atTop,
      (∫ x in A_ann, P_pot (Wj j) x) ≤ (∫ x in A_ann, P_pot V x) + ε / 4 := by
    filter_upwards [hδ_lim.eventually (gt_mem_nhds (half_pos hδ_uc_pos)),
      ht_A_potU.eventually (Iio_mem_nhds (by linarith :
        (∫ x in A_ann, P_pot V x) < (∫ x in A_ann, P_pot V x) + ε / 8))] with j hj_δ hj_U
    have hj_δ' : δ_seq j < δ_uc / 2 := hj_δ
    have hj_U' : (∫ x in A_ann, P_pot (Useq j) x) < (∫ x in A_ann, P_pot V x) + ε / 8 := hj_U
    have hi_c : IntegrableOn (fun _ : Space (m + 1) ↦ ε / (8 * vol_A)) A_ann :=
      continuousOn_const.integrableOn_compact hA_comp
    have hpw_le : (∫ x in A_ann, P_pot (Wj j) x) ≤
        (∫ x in A_ann, P_pot (Useq j) x) + ∫ _x in A_ann, ε / (8 * vol_A) := by
      rw [← integral_add (hiP_on (Useq j) (hUseq_lip j).continuous (hUseq_val j)
        (S := A_ann) sdiff_subset) hi_c]
      apply setIntegral_mono_on (hiP_on (Wj j) (hWj_lip j).continuous (hWj_val j) sdiff_subset)
        ((hiP_on (Useq j) (hUseq_lip j).continuous (hUseq_val j) sdiff_subset).add hi_c)
        (isClosed_closedBall.measurableSet.diff hB_meas)
      intro x hx
      dsimp only [P_pot, Pi.add_apply]
      have hnx : r < ‖x‖ := by
        have hnotb : x ∉ B_in := hx.2
        have hge : r + 1 ≤ ‖x‖ := by
          simpa only [B_in, mem_ball, dist_zero_right, not_lt] using hnotb
        linarith
      have hZV_x : Z x = V x := hZV_eq hnx
      have hvj_le_U : vj j x ≤ Useq j x := by
        dsimp only [vj]
        rw [hZV_x]
        refine max_le ?_ (hUseq_val j x).1
        have hd := (abs_lt.mp (hδ_ge j hx.1)).1
        linarith
      by_cases hpW : 0 < Wj j x
      · have hpU : 0 < Useq j x := by
          by_contra hnotU
          have hU0 : Useq j x = 0 := le_antisymm (not_lt.mp hnotU) (hUseq_val j x).1
          have hv0 : vj j x = 0 := le_antisymm (hvj_le_U.trans_eq hU0) (hvj_val j x).1
          have hW0 : Wj j x = 0 := by
            dsimp only [Wj, gluedCompetitor]
            rw [hU0, hv0]
            ring
          exact hpW.ne' hW0
        rw [indicator_of_mem (s := {y | 0 < Wj j y}) hpW,
          indicator_of_mem (s := {y | 0 < Useq j y}) hpU]
        have hdiff_WU : dist (Wj j x) (Useq j x) < δ_uc := by
          rw [Real.dist_eq]
          have heq : Wj j x - Useq j x = (η : Space (m + 1) → ℝ) x * (vj j x - Useq j x) := by
            dsimp only [Wj, gluedCompetitor]; ring
          rw [heq, abs_mul, abs_of_nonneg η.nonneg]
          have h1 : |vj j x - Useq j x| < 2 * δ_seq j := by
            have hle1 : vj j x ≤ Useq j x := hvj_le_U
            have hge1 : Useq j x - 2 * δ_seq j < vj j x := by
              have hd := (abs_lt.mp (hδ_ge j hx.1)).2
              have hge_max : V x - δ_seq j ≤ vj j x := by
                dsimp only [vj]; rw [hZV_x]; exact le_max_left _ _
              linarith
            rw [abs_of_nonpos (sub_nonpos.mpr hle1)]
            linarith
          exact (mul_le_of_le_one_left (abs_nonneg _) (hη_val x).2).trans_lt
            (h1.trans (by linarith only [hj_δ']))
        have hd_pot := huc (Wj j x) (hWj_val j x) (Useq j x) (hUseq_val j x) hdiff_WU
        rw [Real.dist_eq] at hd_pot
        linarith [(abs_lt.mp hd_pot).2]
      · rw [indicator_of_notMem (s := {y | 0 < Wj j y}) hpW]
        have hU_nn : 0 ≤ {y | 0 < Useq j y}.indicator
            (fun y ↦ normalizedPotential f (Useq j y)) x := by
          by_cases hpU : 0 < Useq j x
          · rw [indicator_of_mem (s := {y | 0 < Useq j y}) hpU]
            exact hr.normalizedPotential_nonneg h (hUseq_val j x)
          · rw [indicator_of_notMem (s := {y | 0 < Useq j y}) hpU]
        have hc_pos : 0 < ε / (8 * vol_A) := div_pos hε (by positivity)
        linarith
    rw [setIntegral_const, smul_eq_mul] at hpw_le
    have hvol_le : volume.real A_ann * (ε / (8 * vol_A)) ≤ ε / 8 := by
      have h1 : volume.real A_ann ≤ vol_A := by dsimp only [vol_A]; linarith
      calc
        volume.real A_ann * (ε / (8 * vol_A))
          ≤ vol_A * (ε / (8 * vol_A)) :=
            mul_le_mul_of_nonneg_right h1 (div_nonneg hε.le (by positivity))
        _ = ε / 8 := by field_simp [hvol_A_pos.ne']
    linarith
  -- Kinetic bound on `A_ann`
  let KV_int : ℝ := (∫ x in A_ann, ‖gradient V x‖ ^ 2 / 2) + 1
  have hKV_pos : 0 < KV_int := by
    have h0 : 0 ≤ ∫ x in A_ann, ‖gradient V x‖ ^ 2 / 2 :=
      integral_nonneg (fun _ ↦ by positivity)
    dsimp only [KV_int]; linarith
  let γ_kin : ℝ := ε / (8 * KV_int)
  have hγ_pos : 0 < γ_kin := div_pos hε (by positivity)
  have ht_A_kin := hr.physical_translation_kinetic_tendsto h hV hV_val hlim hA_comp
  have ht_err : Tendsto (fun j ↦
      (1 + γ_kin) * ((∫ x in A_ann,
          ‖‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖) / 2) +
        volume.real A_ann * ((1 + 1 / γ_kin) * (2 * δ_seq j * (Cη : ℝ)) ^ 2 / 2))
      atTop (𝓝 0) := by
    have ht1 : Tendsto (fun j ↦ (1 + γ_kin) * ((∫ x in A_ann,
        ‖‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖) / 2)) atTop (𝓝 0) := by
      simpa only [zero_div, mul_zero] using (ht_A_kin.div_const 2).const_mul (1 + γ_kin)
    have ht2 : Tendsto (fun j ↦ volume.real A_ann *
        ((1 + 1 / γ_kin) * (2 * δ_seq j * (Cη : ℝ)) ^ 2 / 2)) atTop (𝓝 0) := by
      have hd0 : Tendsto (fun j ↦ 2 * δ_seq j * (Cη : ℝ)) atTop (𝓝 0) := by
        simpa only [mul_zero, zero_mul] using (hδ_lim.const_mul 2).mul_const (Cη : ℝ)
      have hsq0 : Tendsto (fun j ↦ (2 * δ_seq j * (Cη : ℝ)) ^ 2) atTop (𝓝 0) := by
        simpa only [sq, mul_zero] using hd0.mul hd0
      simpa only [mul_zero, zero_div] using
        ((hsq0.const_mul (1 + 1 / γ_kin)).div_const 2).const_mul (volume.real A_ann)
    simpa only [add_zero] using ht1.add ht2
  have hev_A_kin : ∀ᶠ j in atTop,
      (∫ x in A_ann, ‖gradient (Wj j) x‖ ^ 2 / 2) ≤
        (∫ x in A_ann, ‖gradient V x‖ ^ 2 / 2) + ε / 4 := by
    filter_upwards [ht_err.eventually (gt_mem_nhds (by positivity : 0 < ε / 8))] with j hj_err
    have hi_kW : IntegrableOn (fun x ↦ ‖gradient (Wj j) x‖ ^ 2 / 2) A_ann :=
      ((integrableOn_gradient_sq_of_locallyLipschitz (hWj_lip j) hK_out).mono_set
        sdiff_subset).div_const 2
    have hi_kV : IntegrableOn (fun x ↦ ‖gradient V x‖ ^ 2 / 2) A_ann :=
      (integrableOn_gradient_sq_of_locallyLipschitz hV.locallyLipschitz hA_comp).div_const 2
    have hi_kdiff : IntegrableOn
        (fun x ↦ ‖‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖) A_ann := by
      have hiU : IntegrableOn (fun x ↦ ‖gradient U (p j + x)‖ ^ 2) A_ann := by
        have hi0 := integrableOn_gradient_sq_of_locallyLipschitz (hUseq_lip j) hA_comp
        exact hi0.congr_fun (fun x _ ↦ by simp [Useq, gradient, fderiv_comp_add_left])
          (isClosed_closedBall.measurableSet.diff hB_meas)
      have hiV := integrableOn_gradient_sq_of_locallyLipschitz hV.locallyLipschitz hA_comp
      exact (Integrable.sub hiU hiV).norm
    let c_tail : ℝ := (1 + 1 / γ_kin) * (2 * δ_seq j * (Cη : ℝ)) ^ 2 / 2
    let dom_fn : Space (m + 1) → ℝ := fun x ↦
      (1 + γ_kin) * (‖gradient V x‖ ^ 2 / 2 +
        ‖‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖ / 2) + c_tail
    have hi_main : IntegrableOn (fun x ↦ (1 + γ_kin) *
        (‖gradient V x‖ ^ 2 / 2 +
          ‖‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖ / 2)) A_ann :=
      (Integrable.add hi_kV (hi_kdiff.div_const 2)).const_mul (1 + γ_kin)
    have hi_ctail : IntegrableOn (fun _ : Space (m + 1) ↦ c_tail) A_ann :=
      continuousOn_const.integrableOn_compact hA_comp
    have hi_dom : IntegrableOn dom_fn A_ann := Integrable.add hi_main hi_ctail
    have hae_A : ∀ᵐ x ∂volume.restrict A_ann, ‖gradient (Wj j) x‖ ^ 2 / 2 ≤ dom_fn x := by
      filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet.diff hB_meas),
        ae_restrict_of_ae (ae_differentiableAt_of_locallyLipschitz (hUseq_lip j)),
        ae_restrict_of_ae (ae_differentiableAt_of_locallyLipschitz (hvj_lip j)),
        ae_restrict_of_ae (hBin_grad_le j)] with x hx hdU hdvj hgvj_le
      have hdη : DifferentiableAt ℝ (η : Space (m + 1) → ℝ) x :=
        (η.contDiff (n := 1)).differentiable one_ne_zero x
      have hng := norm_gradient_gluedCompetitor_le hdU hdvj hdη (hη_val x)
      have hnx : r + 1 ≤ ‖x‖ := by
        have hnotb : x ∉ B_in := hx.2
        simpa only [B_in, mem_ball, dist_zero_right, not_lt] using hnotb
      have hopen_out : IsOpen {y : Space (m + 1) | r + 1 / 2 < ‖y‖} :=
        isOpen_lt continuous_const continuous_norm
      have hev_ZV : Z =ᶠ[𝓝 x] V := by
        filter_upwards [hopen_out.mem_nhds (by linarith : r + 1 / 2 < ‖x‖)] with y hy
        exact hZV_eq (by linarith : r < ‖y‖)
      have hgZ_V : gradient Z x = gradient V x := hev_ZV.gradient_eq
      have hvj_diff_le : ‖vj j x - Useq j x‖ ≤ 2 * δ_seq j := by
        rw [Real.norm_eq_abs]
        have hZV_x : Z x = V x := hZV_eq (by linarith)
        have hd1 := hδ_ge j hx.1
        have hle1 : vj j x ≤ Useq j x := by
          dsimp only [vj]; rw [hZV_x]
          exact max_le (by linarith [(abs_lt.mp hd1).1]) (hUseq_val j x).1
        have hge1 : Useq j x - 2 * δ_seq j ≤ vj j x := by
          have hge_m : V x - δ_seq j ≤ vj j x := by
            dsimp only [vj]; rw [hZV_x]; exact le_max_left _ _
          linarith [(abs_lt.mp hd1).2]
        rw [abs_of_nonpos (sub_nonpos.mpr hle1)]
        linarith
      have hgη_le : ‖gradient (η : Space (m + 1) → ℝ) x‖ ≤ Cη := hCη x hx.1
      have hgU_eq : ‖gradient (Useq j) x‖ = ‖gradient U (p j + x)‖ := by
        simp only [Useq, gradient, fderiv_comp_add_left]
      let A_term : ℝ := (1 - (η : Space (m + 1) → ℝ) x) * ‖gradient U (p j + x)‖ +
        (η : Space (m + 1) → ℝ) x * ‖gradient V x‖
      let B_term : ℝ := 2 * δ_seq j * (Cη : ℝ)
      have hδj_pos : 0 < δ_seq j := hδ_pos j
      have hW_le_AB : ‖gradient (Wj j) x‖ ≤ A_term + B_term := by
        have h1 : (1 - (η : Space (m + 1) → ℝ) x) * ‖gradient (Useq j) x‖ +
            (η : Space (m + 1) → ℝ) x * ‖gradient (vj j) x‖ ≤ A_term := by
          dsimp only [A_term]
          rw [← hgU_eq, ← hgZ_V]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hgvj_le (hη_val x).1)
        have h2 : ‖vj j x - Useq j x‖ * ‖gradient (η : Space (m + 1) → ℝ) x‖ ≤ B_term :=
          mul_le_mul hvj_diff_le hgη_le (norm_nonneg _) (mul_nonneg two_pos.le hδj_pos.le)
        exact hng.trans (add_le_add h1 h2)
      have hconv : A_term ^ 2 ≤
          (1 - (η : Space (m + 1) → ℝ) x) * ‖gradient U (p j + x)‖ ^ 2 +
            (η : Space (m + 1) → ℝ) x * ‖gradient V x‖ ^ 2 := by
        dsimp only [A_term]
        have h0 := (hη_val x).1
        have h1 : 0 ≤ 1 - (η : Space (m + 1) → ℝ) x := sub_nonneg.mpr (hη_val x).2
        have hnn : 0 ≤ (η : Space (m + 1) → ℝ) x * (1 - (η : Space (m + 1) → ℝ) x) *
            (‖gradient U (p j + x)‖ - ‖gradient V x‖) ^ 2 :=
          mul_nonneg (mul_nonneg h0 h1) (sq_nonneg _)
        have hident_c : ((1 - (η : Space (m + 1) → ℝ) x) * ‖gradient U (p j + x)‖ ^ 2 +
            (η : Space (m + 1) → ℝ) x * ‖gradient V x‖ ^ 2) -
            ((1 - (η : Space (m + 1) → ℝ) x) * ‖gradient U (p j + x)‖ +
              (η : Space (m + 1) → ℝ) x * ‖gradient V x‖) ^ 2 =
            (η : Space (m + 1) → ℝ) x * (1 - (η : Space (m + 1) → ℝ) x) *
              (‖gradient U (p j + x)‖ - ‖gradient V x‖) ^ 2 := by ring
        linarith only [hnn, hident_c]
      have hdiff_g : (1 - (η : Space (m + 1) → ℝ) x) * ‖gradient U (p j + x)‖ ^ 2 +
          (η : Space (m + 1) → ℝ) x * ‖gradient V x‖ ^ 2 ≤
          ‖gradient V x‖ ^ 2 + ‖‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖ := by
        rw [Real.norm_eq_abs]
        have hle_abs := le_abs_self (‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2)
        have h1 : 1 - (η : Space (m + 1) → ℝ) x ≤ 1 := sub_le_self 1 (hη_val x).1
        have h1_nn : 0 ≤ 1 - (η : Space (m + 1) → ℝ) x := sub_nonneg.mpr (hη_val x).2
        have hident : (1 - (η : Space (m + 1) → ℝ) x) * ‖gradient U (p j + x)‖ ^ 2 +
            (η : Space (m + 1) → ℝ) x * ‖gradient V x‖ ^ 2 =
            ‖gradient V x‖ ^ 2 +
              (1 - (η : Space (m + 1) → ℝ) x) *
                (‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2) := by ring
        rw [hident]
        exact add_le_add le_rfl
          ((mul_le_mul_of_nonneg_left hle_abs h1_nn).trans
            (mul_le_of_le_one_left (abs_nonneg _) h1))
      have hsq_W : ‖gradient (Wj j) x‖ ^ 2 ≤ (A_term + B_term) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hW_le_AB 2
      have hyoung : (A_term + B_term) ^ 2 ≤
          (1 + γ_kin) * A_term ^ 2 + (1 + 1 / γ_kin) * B_term ^ 2 := by
        have hnn : 0 ≤ γ_kin * (A_term - B_term / γ_kin) ^ 2 :=
          mul_nonneg hγ_pos.le (sq_nonneg _)
        have hid : (1 + γ_kin) * A_term ^ 2 + (1 + 1 / γ_kin) * B_term ^ 2 -
            (A_term + B_term) ^ 2 = γ_kin * (A_term - B_term / γ_kin) ^ 2 := by
          field_simp [hγ_pos.ne']; ring
        linarith only [hnn, hid]
      have hA_le : A_term ^ 2 ≤ ‖gradient V x‖ ^ 2 +
          ‖‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖ := hconv.trans hdiff_g
      have hcomb : ‖gradient (Wj j) x‖ ^ 2 ≤
          (1 + γ_kin) * (‖gradient V x‖ ^ 2 +
            ‖‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖) +
            (1 + 1 / γ_kin) * B_term ^ 2 :=
        (hsq_W.trans hyoung).trans
          (add_le_add (mul_le_mul_of_nonneg_left hA_le (by linarith only [hγ_pos])) le_rfl)
      dsimp only [dom_fn, c_tail, B_term] at hcomb ⊢
      linarith only [hcomb]
    have hint_le := integral_mono_ae hi_kW hi_dom hae_A
    have hdom_eval : (∫ x in A_ann, dom_fn x) =
        (1 + γ_kin) * ((∫ x in A_ann, ‖gradient V x‖ ^ 2 / 2) +
          (∫ x in A_ann, ‖‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖) / 2) +
          volume.real A_ann * c_tail := by
      dsimp only [dom_fn]
      rw [integral_add hi_main hi_ctail, integral_const_mul,
        integral_add hi_kV (hi_kdiff.div_const 2), setIntegral_const, smul_eq_mul]
      congr 3
      exact integral_div 2 _
    rw [hdom_eval] at hint_le
    have hγ_KV : γ_kin * (∫ x in A_ann, ‖gradient V x‖ ^ 2 / 2) ≤ ε / 8 := by
      have hle_KV : (∫ x in A_ann, ‖gradient V x‖ ^ 2 / 2) ≤ KV_int := by
        dsimp only [KV_int]; linarith only
      calc
        γ_kin * (∫ x in A_ann, ‖gradient V x‖ ^ 2 / 2)
          ≤ γ_kin * KV_int := mul_le_mul_of_nonneg_left hle_KV hγ_pos.le
        _ = ε / 8 := by dsimp only [γ_kin]; field_simp [hKV_pos.ne']
    have hj_err' : (1 + γ_kin) * ((∫ x in A_ann,
          ‖‖gradient U (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖) / 2) +
        volume.real A_ann * c_tail < ε / 8 := hj_err
    linarith only [hint_le, hγ_KV, hj_err']
  -- Combine `ht_Useq`, `hev_Bin`, `hev_A_pot`, `hev_A_kin` at a large index `j`
  obtain ⟨j, ⟨⟨hj_U, hj_Bin⟩, hj_Apot⟩, hj_Akin⟩ :=
    (((ht_Useq.eventually (Ioi_mem_nhds (by linarith :
        (∫ x in K_out, phaseEnergyDensity f 0 V x) - ε / 4 <
          ∫ x in K_out, phaseEnergyDensity f 0 V x))).and hev_Bin).and hev_A_pot).and
      hev_A_kin |>.exists
  have hj_U' : (∫ x in K_out, phaseEnergyDensity f 0 V x) - ε / 4 <
      ∫ x in K_out, phaseEnergyDensity f 0 (Useq j) x := hj_U
  have hi_Wj := h.integrableOn_lipschitz_phaseEnergy (hWj_lip j) (hWj_val j) 0 hK_out
  have hi_Z := h.integrableOn_lipschitz_phaseEnergy hZ hZ_val 0 hK_out
  have hi_V := h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hV_val 0 hK_out
  have hA_Wj_split : (∫ x in A_ann, phaseEnergyDensity f 0 (Wj j) x) =
      (∫ x in A_ann, ‖gradient (Wj j) x‖ ^ 2 / 2) + ∫ x in A_ann, P_pot (Wj j) x := by
    have hc : Set.EqOn (phaseEnergyDensity f 0 (Wj j))
        (fun x ↦ ‖gradient (Wj j) x‖ ^ 2 / 2 + P_pot (Wj j) x) A_ann :=
      fun x _ ↦ phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hWj_val j y).1) f x
    rw [setIntegral_congr_fun (isClosed_closedBall.measurableSet.diff hB_meas) hc,
      integral_add (((integrableOn_gradient_sq_of_locallyLipschitz (hWj_lip j) hK_out).mono_set
        sdiff_subset).div_const 2) (hiP_on (Wj j) (hWj_lip j).continuous (hWj_val j) sdiff_subset)]
  have hA_V_split : (∫ x in A_ann, phaseEnergyDensity f 0 V x) =
      (∫ x in A_ann, ‖gradient V x‖ ^ 2 / 2) + ∫ x in A_ann, P_pot V x := by
    have hc : Set.EqOn (phaseEnergyDensity f 0 V)
        (fun x ↦ ‖gradient V x‖ ^ 2 / 2 + P_pot V x) A_ann :=
      fun x _ ↦ phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hV_val y).1) f x
    rw [setIntegral_congr_fun (isClosed_closedBall.measurableSet.diff hB_meas) hc,
      integral_add ((integrableOn_gradient_sq_of_locallyLipschitz hV.locallyLipschitz
        hA_comp).div_const 2) (hiP_on V hV.continuous hV_val sdiff_subset)]
  have hm := hmin_j j
  rw [hsplit_int (phaseEnergyDensity f 0 (Wj j)) hi_Wj] at hm
  have hZ_split := hsplit_int (phaseEnergyDensity f 0 Z) hi_Z
  linarith [hAZ_eq, hA_Wj_split, hA_V_split]

/-- **Modica logarithmic equilibrium barrier**:
Modica's gradient estimate `‖∇u‖² / 2 ≤ W(u)` and the quadratic upper bound `W(s) ≤ C (1 - s)²`
yield a global exponential Harnack inequality for `1 - zeroExtension g u`, which passes to every
physical translation limit `V`. -/
theorem RigidityHypotheses.exists_equilibrium_distance_exp_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ L_mod : ℝ, 0 < L_mod ∧
      ∀ (p : ℕ → Space (m + 1)) (V : Space (m + 1) → ℝ),
        (∀ K : Set (Space (m + 1)), IsCompact K →
          TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K) →
        ∀ x y : Space (m + 1),
          (1 - V x) * Real.exp (-L_mod * dist y x) ≤ 1 - V y := by
  obtain ⟨C, hC, hW_le⟩ := hr.potential_quadratic_upper_bound h
  let L_mod : ℝ := Real.sqrt (2 * C)
  have hL_pos : 0 < L_mod := Real.sqrt_pos.mpr (by positivity)
  let U := zeroExtension g u
  -- First prove `-log (1 - U y) ≤ -log (1 - U x) + L_mod * dist y x` for all `x, y`
  have hU_log (x y : Space (m + 1)) :
      -Real.log (1 - U y) ≤ -Real.log (1 - U x) + L_mod * dist y x := by
    have hU_lt (z : Space (m + 1)) : 0 < 1 - U z := sub_pos.mpr (hr.zeroExtension_lt_one z)
    have hU_le1 (z : Space (m + 1)) : 1 - U z ≤ 1 := by linarith [h.zeroExtension_nonneg z]
    have hlog_nn (z : Space (m + 1)) : 0 ≤ -Real.log (1 - U z) :=
      neg_nonneg.mpr (Real.log_nonpos (hU_lt z).le (hU_le1 z))
    by_cases hy : y ∈ epigraph g
    · let γ : ℝ → Space (m + 1) := fun t ↦ (1 - t) • x + t • y
      have hγ_cont : Continuous γ := by fun_prop
      let φ : ℝ → ℝ := fun t ↦ -Real.log (1 - U (γ t))
      have hφ_cont : Continuous φ :=
        (((continuous_const.sub (h.zeroExtension_continuous.comp hγ_cont)).log
          (fun t ↦ (hU_lt (γ t)).ne')).neg)
      -- Derivative bound of `φ` at any `t` with `γ t ∈ epigraph g`
      have hφ_deriv {t : ℝ} (ht_in : γ t ∈ epigraph g) :
          DifferentiableAt ℝ φ t ∧ deriv φ t ≤ L_mod * dist y x := by
        have hΩ := isOpen_epigraph h.graph_contDiff.continuous
        have hev_U : U =ᶠ[𝓝 (γ t)] u := by
          filter_upwards [hΩ.mem_nhds ht_in] with z hz
          exact zeroExtension_of_mem hz
        have hγ_d : HasFDerivAt γ ((ContinuousLinearMap.id ℝ ℝ).smulRight (y - x)) t := by
          have hd1 : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t :=
            ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).congr_deriv (by ring)
          have hd_smul1 : HasDerivAt (fun s : ℝ ↦ (1 - s) • x) ((-1 : ℝ) • x) t :=
            hd1.smul_const x
          have hd_smul2 : HasDerivAt (fun s : ℝ ↦ s • y) ((1 : ℝ) • y) t :=
            (hasDerivAt_id t).smul_const y
          exact ((hd_smul1.add hd_smul2).congr_deriv (by module)).hasFDerivAt
        have hu_d : DifferentiableAt ℝ u (γ t) :=
          ((h.solution_contDiffOn.of_le (by norm_num)).differentiableOn_one (γ t)
            ht_in).differentiableAt (hΩ.mem_nhds ht_in)
        have hU_γ : HasDerivAt (fun s ↦ U (γ s)) (inner ℝ (gradient u (γ t)) (y - x)) t := by
          have hu_γ : HasDerivAt (fun s ↦ u (γ s)) (fderiv ℝ u (γ t) (y - x)) t := by
            have hc := (hu_d.hasFDerivAt.comp t hγ_d).hasDerivAt
            exact hc.congr_deriv (by simp)
          have hgrad_in : fderiv ℝ u (γ t) (y - x) = inner ℝ (gradient u (γ t)) (y - x) := by
            simp [gradient]
          rw [← hgrad_in]
          exact hu_γ.congr_of_eventuallyEq (hγ_cont.continuousAt.eventually
            (hev_U.mono (fun z hz ↦ hz)))
        have hpos_1u : 0 < 1 - U (γ t) := hU_lt (γ t)
        have hφ_hd : HasDerivAt φ (inner ℝ (gradient u (γ t)) (y - x) / (1 - U (γ t))) t := by
          have hsub_hd : HasDerivAt (fun s ↦ 1 - U (γ s))
              (-inner ℝ (gradient u (γ t)) (y - x)) t := by
            have hs := (hasDerivAt_const t (1 : ℝ)).sub hU_γ
            exact hs.congr_deriv (by ring)
          have hlog_hd := (hsub_hd.log hpos_1u.ne').neg
          exact hlog_hd.congr_deriv (by ring)
        refine ⟨hφ_hd.differentiableAt, ?_⟩
        rw [hφ_hd.deriv]
        have hu_eq : U (γ t) = u (γ t) := zeroExtension_of_mem ht_in
        have hu_mem : u (γ t) ∈ Icc (0 : ℝ) 1 :=
          ⟨(h.positive (γ t) ht_in).le, (hr.solution_lt_one (γ t) ht_in).le⟩
        have hmod := hr.modica_bound h ht_in
        have hpot := hW_le (u (γ t)) hu_mem
        have hg_sq : ‖gradient u (γ t)‖ ^ 2 ≤ (L_mod * (1 - u (γ t))) ^ 2 := by
          dsimp only [L_mod]
          rw [ mul_pow, Real.sq_sqrt (by positivity) ]
          linarith
        have hg_le : ‖gradient u (γ t)‖ ≤ L_mod * (1 - U (γ t)) := by
          rw [hu_eq]
          exact le_of_sq_le_sq hg_sq (mul_nonneg hL_pos.le (sub_pos.mpr
            (hr.solution_lt_one (γ t) ht_in)).le)
        have hin_le : inner ℝ (gradient u (γ t)) (y - x) ≤
            (L_mod * (1 - U (γ t))) * dist y x := by
          rw [dist_eq_norm]
          exact (real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right hg_le (norm_nonneg _))
        exact (div_le_iff₀ hpos_1u).mpr (by linarith)
      let S_out : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | γ t ∉ epigraph g}
      rcases S_out.eq_empty_or_nonempty with hemp | hne
      · have hall_in (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ epigraph g := by
          by_contra hnot
          have hmem : t ∈ S_out := ⟨ht, hnot⟩
          rw [hemp] at hmem
          exact notMem_empty t hmem
        obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope φ zero_lt_one hφ_cont.continuousOn
          (fun t ht ↦ (hφ_deriv (hall_in t ⟨ht.1.le, ht.2.le⟩)).1.differentiableWithinAt)
        have hd_le := (hφ_deriv (hall_in ξ ⟨hξ.1.le, hξ.2.le⟩)).2
        have hγ0 : γ 0 = x := by simp [γ]
        have hγ1 : γ 1 = y := by simp [γ]
        have hφ_diff : φ 1 - φ 0 = deriv φ ξ := by linarith [div_one (φ 1 - φ 0)]
        dsimp only [φ] at hφ_diff
        rw [hγ0, hγ1] at hφ_diff
        linarith [dist_nonneg (x := y) (y := x)]
      · have hS_closed : IsClosed S_out :=
          isClosed_Icc.inter ((isOpen_epigraph h.graph_contDiff.continuous).isClosed_compl.preimage
            hγ_cont)
        have hS_bdd : BddAbove S_out := ⟨1, fun _ ht ↦ ht.1.2⟩
        let t₀ : ℝ := sSup S_out
        have ht₀_mem : t₀ ∈ S_out := hS_closed.csSup_mem hne hS_bdd
        have ht₀_lt : t₀ < 1 := by
          apply lt_of_le_of_ne ht₀_mem.1.2
          intro heq1
          apply ht₀_mem.2
          rw [heq1]
          simpa [γ] using hy
        have hall_in (t : ℝ) (ht : t ∈ Ioo t₀ 1) : γ t ∈ epigraph g := by
          by_contra hnot
          have hm : t ∈ S_out := ⟨⟨ht₀_mem.1.1.trans ht.1.le, ht.2.le⟩, hnot⟩
          exact (not_le_of_gt ht.1) (le_csSup hS_bdd hm)
        obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope φ ht₀_lt hφ_cont.continuousOn
          (fun t ht ↦ (hφ_deriv (hall_in t ht)).1.differentiableWithinAt)
        have hd_le := (hφ_deriv (hall_in ξ hξ)).2
        have hφ_t₀ : φ t₀ = 0 := by
          dsimp only [φ, U]
          rw [zeroExtension_of_notMem ht₀_mem.2, sub_zero, Real.log_one, neg_zero]
        have hγ1 : γ 1 = y := by simp [γ]
        have hsub_pos : 0 < 1 - t₀ := sub_pos.mpr ht₀_lt
        have hmul_eq : φ 1 - φ t₀ = (1 - t₀) * deriv φ ξ := by
          have h1 := (eq_div_iff hsub_pos.ne').mp hslope
          linarith
        have hle_prod : (1 - t₀) * deriv φ ξ ≤ L_mod * dist y x := by
          calc
            (1 - t₀) * deriv φ ξ ≤ (1 - t₀) * (L_mod * dist y x) :=
              mul_le_mul_of_nonneg_left hd_le hsub_pos.le
            _ ≤ 1 * (L_mod * dist y x) :=
              mul_le_mul_of_nonneg_right (by linarith [ht₀_mem.1.1])
                (mul_nonneg hL_pos.le dist_nonneg)
            _ = L_mod * dist y x := one_mul _
        have hφ1_eq : φ 1 = -Real.log (1 - U y) := by dsimp only [φ]; rw [hγ1]
        linarith [hlog_nn x]
    · dsimp only [U]
      rw [zeroExtension_of_notMem hy, sub_zero, Real.log_one, neg_zero]
      exact add_nonneg (hlog_nn x) (mul_nonneg hL_pos.le dist_nonneg)
  refine ⟨L_mod, hL_pos, fun p V hlim x y ↦ ?_⟩
  have hpt (z : Space (m + 1)) :
      Tendsto (fun j ↦ U (p j + z)) atTop (𝓝 (V z)) :=
    (hlim {z} isCompact_singleton).tendsto_at (mem_singleton z)
  have ht_lhs : Tendsto
      (fun j ↦ (1 - U (p j + x)) * Real.exp (-L_mod * dist y x)) atTop
      (𝓝 ((1 - V x) * Real.exp (-L_mod * dist y x))) :=
    ((tendsto_const_nhds.sub (hpt x)).mul_const _)
  have ht_rhs : Tendsto (fun j ↦ 1 - U (p j + y)) atTop (𝓝 (1 - V y)) :=
    tendsto_const_nhds.sub (hpt y)
  apply le_of_tendsto_of_tendsto ht_lhs ht_rhs
  refine Eventually.of_forall (fun j ↦ ?_)
  have hlog_j := hU_log (p j + x) (p j + y)
  rw [dist_add_left] at hlog_j
  have hpos_x : 0 < 1 - U (p j + x) := sub_pos.mpr (hr.zeroExtension_lt_one _)
  have hpos_y : 0 < 1 - U (p j + y) := sub_pos.mpr (hr.zeroExtension_lt_one _)
  have hexp_le : Real.exp (Real.log (1 - U (p j + x)) - L_mod * dist y x) ≤
      Real.exp (Real.log (1 - U (p j + y))) :=
    Real.exp_le_exp.mpr (by linarith)
  dsimp only
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hpos_x, Real.exp_log hpos_y] at hexp_le
  simpa only [neg_mul] using hexp_le

/-- If a physical translation limit `V` takes a value `< 1` at one point, then `V < 1` everywhere
and `{x | 0 < V x} ≠ univ` (hence `(frontier {x | 0 < V x}).Nonempty` when `{0 < V}` is nonempty). -/
theorem RigidityHypotheses.physical_translation_limit_lt_one_and_not_univ
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)}
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {x₀ : Space (m + 1)} (hx₀ : V x₀ < 1) :
    (∀ y, V y < 1) ∧ {x | 0 < V x} ≠ univ := by
  obtain ⟨L_mod, _, hexp⟩ := hr.exists_equilibrium_distance_exp_bound h
  have hlt_all (y : Space (m + 1)) : V y < 1 := by
    have h1 := hexp p V hlim x₀ y
    have hpos : 0 < (1 - V x₀) * Real.exp (-L_mod * dist y x₀) :=
      mul_pos (sub_pos.mpr hx₀) (Real.exp_pos _)
    linarith
  refine ⟨hlt_all, fun huniv ↦ ?_⟩
  have hVx₀_pos : 0 < V x₀ := by
    have hm : x₀ ∈ {x | 0 < V x} := by rw [huniv]; exact mem_univ x₀
    exact hm
  let a : ℝ := (V x₀ + 1) / 2
  have ha_mem : a ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp only [a]; linarith, by dsimp only [a]; linarith⟩
  have hfa_pos : 0 < f a := hr.reaction_pos a ha_mem
  let N : ℝ := (Module.finrank ℝ (Space (m + 1)) : ℝ) + 2
  have hN_pos : 0 < N := by dsimp only [N]; positivity
  let q : ℝ := f a / a
  have hq_pos : 0 < q := div_pos hfa_pos ha_mem.1
  let R : ℝ := N / Real.sqrt q + 1
  have hR_pos : 0 < R := by dsimp only [R]; positivity
  have hgap : N ^ 2 / R ^ 2 < f a / a := by
    have hgt : N / Real.sqrt q < R := by dsimp only [R]; linarith
    have h1 : N < R * Real.sqrt q := (div_lt_iff₀ (Real.sqrt_pos.mpr hq_pos)).mp hgt
    have h2 : N ^ 2 < R ^ 2 * (Real.sqrt q) ^ 2 := by nlinarith [Real.sqrt_pos.mpr hq_pos]
    rw [Real.sq_sqrt hq_pos.le] at h2
    exact (div_lt_iff₀ (sq_pos_of_pos hR_pos)).mpr (by simpa only [q, mul_comm] using h2)
  have hV_cont : Continuous V := by
    have hpt (z : Space (m + 1)) :
        Tendsto (fun j ↦ zeroExtension g u (p j + z)) atTop (𝓝 (V z)) :=
      (hlim {z} isCompact_singleton).tendsto_at (mem_singleton z)
    have hlip : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V := by
      apply LipschitzWith.of_dist_le_mul
      intro z₁ z₂
      exact le_of_tendsto ((hpt z₁).dist (hpt z₂))
        (Eventually.of_forall (fun j ↦ by
          simpa only [dist_add_left] using
            (hr.zeroExtension_lipschitzWith h).dist_le_mul (p j + z₁) (p j + z₂)))
    exact hlip.continuous
  obtain ⟨z_min, hz_min, hmin⟩ := (isCompact_closedBall x₀ R).exists_isMinOn
    (nonempty_closedBall.mpr hR_pos.le) hV_cont.continuousOn
  have hm_pos : 0 < V z_min := by
    have hm : z_min ∈ {x | 0 < V x} := by rw [huniv]; exact mem_univ z_min
    exact hm
  have hev_ep : ∀ᶠ j in atTop, closedBall (p j + x₀) R ⊆ epigraph g := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (hlim (closedBall x₀ R) (isCompact_closedBall x₀ R)) (V z_min / 2)
      (half_pos hm_pos)] with j hj
    intro z hz
    have hzx : z - p j ∈ closedBall x₀ R := by
      rw [mem_closedBall, dist_eq_norm] at hz ⊢
      have heq : z - p j - x₀ = z - (p j + x₀) := by abel
      rwa [heq]
    have hd := hj (z - p j) hzx
    have hge : V z_min ≤ V (z - p j) := hmin hzx
    have hpz : p j + (z - p j) = z := by abel
    rw [hpz, Real.dist_eq] at hd
    have hupos : 0 < zeroExtension g u z := by linarith [(abs_lt.mp hd).2]
    exact (h.zeroExtension_pos_iff z).mp hupos
  have hpt_x₀ : Tendsto (fun j ↦ zeroExtension g u (p j + x₀)) atTop (𝓝 (V x₀)) :=
    (hlim {x₀} isCompact_singleton).tendsto_at (mem_singleton x₀)
  have ha_le : a ≤ V x₀ := by
    apply ge_of_tendsto hpt_x₀
    filter_upwards [hev_ep] with j hj
    have hmem_c : p j + x₀ ∈ epigraph g := hj (mem_closedBall_self hR_pos.le)
    rw [zeroExtension_of_mem hmem_c]
    exact h.solution_ge_at_ball_center hR_pos ha_mem.1 hj hgap
  dsimp only [a] at ha_le
  linarith

/-- Classical weak-supersolution property of `u` on `epigraph g`, used to rule out vanishing
limits inside balls contained in `epigraph g`. -/
theorem RigidityHypotheses.exists_solution_weakSupersolution
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ M : ℝ, 0 < M ∧ IsWeakSupersolution volume (epigraph g) M u := by
  obtain ⟨Lf, hLf⟩ := (h.reaction_contDiffOn.mono Icc_subset_Ici_self).exists_lipschitzOnWith
    one_ne_zero (convex_Icc 0 1) isCompact_Icc
  let M : ℝ := (Lf : ℝ) + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨M, hM, isWeakSupersolution_of_classical
    (isOpen_epigraph h.graph_contDiff.continuous) h.solution_contDiffOn (fun x hx ↦ ?_)⟩
  rw [h.equation x hx]
  have hu_mem : u x ∈ Icc (0 : ℝ) 1 :=
    ⟨(h.positive x hx).le, (hr.solution_lt_one x hx).le⟩
  have hf0 : 0 ≤ f 0 := reaction_nonneg_zero h.reaction_contDiffOn h.reaction_structure
  have hd := hLf.dist_le_mul (u x) hu_mem 0 ⟨le_rfl, zero_le_one⟩
  rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hu_mem.1] at hd
  have hlow : f 0 - (Lf : ℝ) * u x ≤ f (u x) := by linarith [(abs_le.mp hd).1]
  dsimp only [M]
  nlinarith [hu_mem.1]

/-- Every boundary point `q ∈ frontier {x | 0 < V x}` of a physical translation limit is
eventually approximated within any radius `δ > 0` by `frontier (epigraph g) - p j`. -/
theorem RigidityHypotheses.eventually_exists_frontier_near_limit_frontier
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hV_val : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {q : Space (m + 1)} (hq : q ∈ frontier {x | 0 < V x}) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∃ y ∈ ball q δ, p j + y ∈ frontier (epigraph g) := by
  have hopen_V : IsOpen {x | 0 < V x} := isOpen_lt continuous_const hV.continuous
  have hVq0 : V q = 0 := by
    have hnot : q ∉ {x | 0 < V x} := by
      rw [frontier, hopen_V.interior_eq] at hq
      exact hq.2
    exact le_antisymm (not_lt.mp hnot) (hV_val q).1
  obtain ⟨z₁, hz₁_pos, hdz₁⟩ := Metric.mem_closure_iff.mp hq.1 (δ / 4) (by positivity)
  have hz₁_ball : z₁ ∈ ball q (δ / 4) := by simpa only [mem_ball, dist_comm] using hdz₁
  let r : ℝ := δ / 2
  have hr_pos : 0 < r := half_pos hδ
  have hq_in_r : q ∈ ball z₁ r := by
    rw [mem_ball]
    have hlt_r : δ / 4 < r := by dsimp only [r]; linarith
    exact hdz₁.trans hlt_r
  have hcb_sub : closedBall z₁ r ⊆ ball q δ := by
    intro y hy
    rw [mem_ball]
    have h1 : dist y z₁ ≤ δ / 2 := hy
    have h2 : dist z₁ q < δ / 4 := hz₁_ball
    linarith [dist_triangle y z₁ q]
  -- Choose a small inner radius `r_in < r / 2` around `z₁` where `V ≥ V z₁ / 2`
  have hev_z₁ : ∀ᶠ y in 𝓝 z₁, V z₁ / 2 < V y :=
    (hV.continuous.continuousAt (x := z₁)).eventually (Ioi_mem_nhds (half_lt_self hz₁_pos))
  obtain ⟨s_in, hs_in, hsv⟩ := Metric.eventually_nhds_iff.mp hev_z₁
  let r_in : ℝ := min (s_in / 2) (r / 4)
  have hr_in_pos : 0 < r_in := lt_min (half_pos hs_in) (by positivity)
  have hV_inner (y : Space (m + 1)) (hy : y ∈ closedBall z₁ r_in) : V z₁ / 2 ≤ V y := by
    have hd : dist y z₁ < s_in :=
      hy.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hs_in))
    exact (hsv hd).le
  obtain ⟨M, hM, hweak_u⟩ := hr.exists_solution_weakSupersolution h
  obtain ⟨α, hα, hparam⟩ := exists_annularBarrier_parameter (E := Space (m + 1)) hr_in_pos hM.le
  let ε_in : ℝ := V z₁ / 4
  have hε_in : 0 < ε_in := div_pos hz₁_pos (by norm_num)
  let η_low : ℝ := ε_in * annularBarrier z₁ α r q
  have hη_low_pos : 0 < η_low :=
    mul_pos hε_in (annularBarrier_pos hα hr_pos.le
      (by simpa only [mem_ball, dist_eq_norm] using hq_in_r))
  have hpt_q : Tendsto (fun j ↦ zeroExtension g u (p j + q)) atTop (𝓝 0) := by
    rw [← hVq0]
    exact (hlim {q} isCompact_singleton).tendsto_at (mem_singleton q)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (hlim (closedBall z₁ r_in) (isCompact_closedBall z₁ r_in)) ε_in hε_in,
    hpt_q.eventually (Iio_mem_nhds hη_low_pos)] with j hj_in hj_q
  have hu_in (w : Space (m + 1)) (hw : w ∈ closedBall (p j + z₁) r_in) :
      ε_in ≤ zeroExtension g u w ∧ w ∈ epigraph g := by
    have hw' : w - p j ∈ closedBall z₁ r_in := by
      rw [mem_closedBall, dist_eq_norm] at hw ⊢
      have heq : w - p j - z₁ = w - (p j + z₁) := by abel
      rwa [heq]
    have hd := hj_in (w - p j) hw'
    have hv := hV_inner (w - p j) hw'
    have hpz : p j + (w - p j) = w := by abel
    rw [hpz, Real.dist_eq] at hd
    have hge : ε_in ≤ zeroExtension g u w := by
      dsimp only [ε_in] at hd ⊢
      linarith [(abs_lt.mp hd).2]
    exact ⟨hge, (h.zeroExtension_pos_iff w).mp (hε_in.trans_le hge)⟩
  have hz₁_ep : p j + z₁ ∈ epigraph g :=
    (hu_in (p j + z₁) (mem_closedBall_self hr_in_pos.le)).2
  have hnot_all : ∃ z₂ ∈ closedBall z₁ r, p j + z₂ ∉ epigraph g := by
    by_contra hall
    push Not at hall
    have hball_ep : closedBall (p j + z₁) r ⊆ epigraph g := by
      intro w hw
      have hw' : w - p j ∈ closedBall z₁ r := by
        rw [mem_closedBall, dist_eq_norm] at hw ⊢
        have heq : w - p j - z₁ = w - (p j + z₁) := by abel
        rwa [heq]
      have hpz : p j + (w - p j) = w := by abel
      rw [← hpz]
      exact hall (w - p j) hw'
    have hcomp := hweak_u.annularBarrier_le (isOpen_epigraph h.graph_contDiff.continuous)
      (h.solution_contDiffOn.of_le (by norm_num)) (fun w hw ↦ (h.positive w hw).le)
      hball_ep hM hα hε_in hr_in_pos.le hr_pos.le hparam
      (fun w hw ↦ by
        rw [← zeroExtension_of_mem (u := u) (hu_in w hw).2]
        exact (hu_in w hw).1)
      (p j + q) (by simpa only [mem_ball, dist_add_left] using hq_in_r)
    have hbar_eq : annularBarrier (p j + z₁) α r (p j + q) = annularBarrier z₁ α r q := by
      simp only [annularBarrier, radialGaussian]
      have heq : p j + q - (p j + z₁) = q - z₁ := by abel
      rw [heq]
    have hq_ep : p j + q ∈ epigraph g := hball_ep (ball_subset_closedBall
      (by simpa only [mem_ball, dist_add_left] using hq_in_r))
    rw [hbar_eq, ← zeroExtension_of_mem (u := u) hq_ep] at hcomp
    have hj_q_lt : zeroExtension g u (p j + q) < η_low := hj_q
    dsimp only [η_low] at hj_q_lt
    linarith
  obtain ⟨z₂, hz₂_cb, hz₂_out⟩ := hnot_all
  -- First exit along the segment from `z₁` to `z₂` inside `closedBall z₁ r ⊆ ball q δ`
  let γ : ℝ → Space (m + 1) := fun t ↦ (1 - t) • z₁ + t • z₂
  have hγ_cont : Continuous γ := by fun_prop
  let S : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | p j + γ t ∉ epigraph g}
  have hS_closed : IsClosed S :=
    isClosed_Icc.inter ((isOpen_epigraph h.graph_contDiff.continuous).isClosed_compl.preimage
      (continuous_const.add hγ_cont))
  have hS_ne : S.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by simpa [γ] using hz₂_out⟩
  have hS_bdd : BddBelow S := ⟨0, fun _ ht ↦ ht.1.1⟩
  let t_star : ℝ := sInf S
  have ht_mem : t_star ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have ht_pos : 0 < t_star := by
    apply lt_of_le_of_ne ht_mem.1.1
    intro h0
    apply ht_mem.2
    rw [← h0]
    simpa [γ] using hz₁_ep
  have hcl : p j + γ t_star ∈ closure (epigraph g) := by
    have hmap : MapsTo (fun t : ℝ ↦ p j + γ t) (Ioo 0 t_star) (epigraph g) := by
      intro t ht
      by_contra hnot
      exact (not_le_of_gt ht.2) (csInf_le hS_bdd ⟨⟨ht.1.le, ht.2.le.trans ht_mem.1.2⟩, hnot⟩)
    apply hmap.closure (continuous_const.add hγ_cont)
    rw [closure_Ioo ht_pos.ne]
    exact ⟨ht_pos.le, le_rfl⟩
  have hfront : p j + γ t_star ∈ frontier (epigraph g) := by
    rw [frontier, (isOpen_epigraph h.graph_contDiff.continuous).interior_eq]
    exact ⟨hcl, ht_mem.2⟩
  have hγ_cb : γ t_star ∈ closedBall z₁ r :=
    (convex_closedBall z₁ r) (mem_closedBall_self hr_pos.le) hz₂_cb
      (sub_nonneg.mpr ht_mem.1.2) ht_mem.1.1 (sub_add_cancel 1 t_star)
  exact ⟨γ t_star, hcb_sub hγ_cb, hfront⟩

/-- **Inheritance of uniform coarse positive and negative cones by physical translation limits**:
Under `HasUniformBoundaryCoarseCone g e` (`‖e‖ = 1`), there exists `R_cone > 0` such that at
every `q ∈ frontier {x | 0 < V x}` and every `w` with `R_cone ≤ ‖w‖`:
- `(1 / 4) * ‖w‖ ≤ inner ℝ e w → 1 / 2 ≤ V (q + w)` (hence `0 < V (q + w)`), and
- `inner ℝ e w ≤ -(1 / 4) * ‖w‖ → V (q + w) = 0`. -/
theorem RigidityHypotheses.physical_translation_limit_coarse_cone
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hcone : HasUniformBoundaryCoarseCone g e)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hV_val : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K) :
    ∃ R_cone : ℝ, 0 < R_cone ∧
      ∀ q ∈ frontier {x | 0 < V x}, ∀ w : Space (m + 1), R_cone ≤ ‖w‖ →
        ((1 / 4 : ℝ) * ‖w‖ ≤ inner ℝ e w → (1 / 2 : ℝ) ≤ V (q + w)) ∧
        (inner ℝ e w ≤ -(1 / 4 : ℝ) * ‖w‖ → V (q + w) = 0) := by
  obtain ⟨R₀, hR₀, hR₀_cone⟩ := hcone (1 / 16) (by norm_num)
  have hf_half : 0 < f (1 / 2) := hr.reaction_pos (1 / 2) (by norm_num)
  let N : ℝ := (Module.finrank ℝ (Space (m + 1)) : ℝ) + 2
  have hN_pos : 0 < N := by dsimp only [N]; positivity
  let q_rate : ℝ := f (1 / 2) / (1 / 2 : ℝ)
  have hq_pos : 0 < q_rate := div_pos hf_half (by norm_num)
  let R_ball : ℝ := N / Real.sqrt q_rate + 1
  have hR_ball : 0 < R_ball := by dsimp only [R_ball]; positivity
  have hgap_half : N ^ 2 / R_ball ^ 2 < f (1 / 2) / (1 / 2 : ℝ) := by
    have hgt : N / Real.sqrt q_rate < R_ball := by dsimp only [R_ball]; linarith
    have h1 : N < R_ball * Real.sqrt q_rate := (div_lt_iff₀ (Real.sqrt_pos.mpr hq_pos)).mp hgt
    have h2 : N ^ 2 < R_ball ^ 2 * (Real.sqrt q_rate) ^ 2 := by
      nlinarith [Real.sqrt_pos.mpr hq_pos]
    rw [Real.sq_sqrt hq_pos.le] at h2
    exact (div_lt_iff₀ (sq_pos_of_pos hR_ball)).mpr (by simpa only [q_rate, mul_comm] using h2)
  let R_cone : ℝ := 32 * (R₀ + R_ball + 1)
  have hR_cone : 0 < R_cone := by dsimp only [R_cone]; positivity
  refine ⟨R_cone, hR_cone, fun q hq w hw ↦ ⟨?_, ?_⟩⟩
  · intro hw_in
    have hev_front := hr.eventually_exists_frontier_near_limit_frontier h hV hV_val hlim
      hq zero_lt_one
    have hpt : Tendsto (fun j ↦ zeroExtension g u (p j + (q + w))) atTop (𝓝 (V (q + w))) :=
      (hlim {q + w} isCompact_singleton).tendsto_at (mem_singleton (q + w))
    apply ge_of_tendsto hpt
    filter_upwards [hev_front] with j ⟨yj, hyj_ball, hyj_front⟩
    have hqy : ‖q - yj‖ < 1 := by simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hyj_ball
    have hball_ep : closedBall (p j + (q + w)) R_ball ⊆ epigraph g := by
      intro z hz
      let v_shift : Space (m + 1) := (z - (p j + (q + w))) + (q - yj)
      let w' : Space (m + 1) := w + v_shift
      have hv_norm : ‖v_shift‖ ≤ R_ball + 1 := by
        have h1 : ‖z - (p j + (q + w))‖ ≤ R_ball := by
          simpa only [mem_closedBall, dist_eq_norm] using hz
        exact (norm_add_le _ _).trans (by linarith)
      have hw'_ge : R₀ ≤ ‖w'‖ := by
        have htri : ‖w‖ ≤ ‖w'‖ + ‖v_shift‖ := by
          have heq : w = w' - v_shift := by dsimp only [w']; abel
          rw [heq]; exact norm_sub_le w' v_shift
        dsimp only [R_cone] at hw
        linarith
      have hw'_le : ‖w'‖ ≤ ‖w‖ + R_ball + 1 :=
        (norm_add_le w v_shift).trans (by linarith)
      have hw'_in : (1 / 16 : ℝ) * ‖w'‖ ≤ inner ℝ e w' := by
        have hv_in : -‖v_shift‖ ≤ inner ℝ e v_shift := by
          have hneg : inner ℝ e (-v_shift) ≤ ‖v_shift‖ := by
            simpa only [he, one_mul, norm_neg] using real_inner_le_norm e (-v_shift)
          rw [inner_neg_right] at hneg
          linarith
        have hrew : inner ℝ e w' = inner ℝ e w + inner ℝ e v_shift := by
          dsimp only [w']; rw [inner_add_right]
        rw [hrew]
        dsimp only [R_cone] at hw
        linarith
      have hmem := (hR₀_cone (p j + yj) hyj_front w' hw'_ge).1 hw'_in
      have heq_z : (p j + yj) + w' = z := by dsimp only [w', v_shift]; abel
      rwa [heq_z] at hmem
    have hcenter_ep : p j + (q + w) ∈ epigraph g := hball_ep (mem_closedBall_self hR_ball.le)
    rw [zeroExtension_of_mem hcenter_ep]
    exact h.solution_ge_at_ball_center hR_ball (by norm_num) hball_ep hgap_half
  · intro hw_out
    have hev_front := hr.eventually_exists_frontier_near_limit_frontier h hV hV_val hlim
      hq zero_lt_one
    have hpt : Tendsto (fun j ↦ zeroExtension g u (p j + (q + w))) atTop (𝓝 (V (q + w))) :=
      (hlim {q + w} isCompact_singleton).tendsto_at (mem_singleton (q + w))
    apply tendsto_nhds_unique hpt
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev_front] with j ⟨yj, hyj_ball, hyj_front⟩
    have hqy : ‖q - yj‖ < 1 := by simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hyj_ball
    let w' : Space (m + 1) := w + (q - yj)
    have hw'_ge : R₀ ≤ ‖w'‖ := by
      have htri : ‖w‖ ≤ ‖w'‖ + ‖q - yj‖ := by
        have heq : w = w' - (q - yj) := by dsimp only [w']; abel
        rw [heq]; exact norm_sub_le w' (q - yj)
      dsimp only [R_cone] at hw
      linarith
    have hw'_le : ‖w'‖ ≤ ‖w‖ + 1 := (norm_add_le w (q - yj)).trans (by linarith)
    have hw'_out : inner ℝ e w' ≤ -(1 / 16 : ℝ) * ‖w'‖ := by
      have hqy_in : inner ℝ e (q - yj) ≤ 1 := by
        have h1 : inner ℝ e (q - yj) ≤ ‖q - yj‖ := by
          simpa only [he, one_mul] using real_inner_le_norm e (q - yj)
        linarith
      have hrew : inner ℝ e w' = inner ℝ e w + inner ℝ e (q - yj) := by
        dsimp only [w']; rw [inner_add_right]
      rw [hrew]
      dsimp only [R_cone] at hw
      linarith
    have hnotMem := (hR₀_cone (p j + yj) hyj_front w' hw'_ge).2 hw'_out
    have heq_z : (p j + yj) + w' = p j + (q + w) := by dsimp only [w']; abel
    rw [heq_z] at hnotMem
    exact (zeroExtension_of_notMem hnotMem).symm

/-- Restricting a `κ`-Lipschitz nonnegative function `V` to an open subset `C₁ ⊆ {0 < V}` whose
frontier lies in `{V = 0}` produces a globally `κ`-Lipschitz function on `Space d`. -/
theorem lipschitzWith_piece_of_frontier_zero {d : ℕ} {V : Space d → ℝ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hV0 : ∀ x, 0 ≤ V x)
    {C₁ : Set (Space d)} [DecidablePred (· ∈ C₁)] (hC₁_open : IsOpen C₁)
    (hfront_zero : ∀ z ∈ frontier C₁, V z = 0) :
    LipschitzWith L (fun x ↦ if x ∈ C₁ then V x else 0) := by
  let VC : Space d → ℝ := fun x ↦ if x ∈ C₁ then V x else 0
  have hseg {x y : Space d} (hx : x ∈ C₁) (hy : y ∉ C₁) :
      dist (VC x) (VC y) ≤ (L : ℝ) * dist x y := by
    let γ : ℝ → Space d := fun t ↦ (1 - t) • x + t • y
    have hγ_cont : Continuous γ := by fun_prop
    let S : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | γ t ∉ C₁}
    have hS_closed : IsClosed S := isClosed_Icc.inter (hC₁_open.isClosed_compl.preimage hγ_cont)
    have hS_ne : S.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by simpa [γ] using hy⟩
    have hS_bdd : BddBelow S := ⟨0, fun _ ht ↦ ht.1.1⟩
    let t_star : ℝ := sInf S
    have ht_mem : t_star ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
    have ht_pos : 0 < t_star := by
      apply lt_of_le_of_ne ht_mem.1.1
      intro h0
      apply ht_mem.2
      rw [← h0]
      simpa [γ] using hx
    have hcl : γ t_star ∈ closure C₁ := by
      have hmap : MapsTo γ (Ioo 0 t_star) C₁ := by
        intro t ht
        by_contra hnot
        exact (not_le_of_gt ht.2) (csInf_le hS_bdd ⟨⟨ht.1.le, ht.2.le.trans ht_mem.1.2⟩, hnot⟩)
      apply hmap.closure hγ_cont
      rw [closure_Ioo ht_pos.ne]
      exact ⟨ht_pos.le, le_rfl⟩
    have hfront : γ t_star ∈ frontier C₁ := by
      rw [frontier, hC₁_open.interior_eq]
      exact ⟨hcl, ht_mem.2⟩
    have hVz : V (γ t_star) = 0 := hfront_zero (γ t_star) hfront
    have hd_γ : dist x (γ t_star) = t_star * dist x y := by
      rw [dist_eq_norm, dist_eq_norm]
      have heq : x - γ t_star = t_star • (x - y) := by dsimp only [γ]; module
      rw [heq, norm_smul, Real.norm_of_nonneg ht_pos.le]
    have hlip_z := hV.dist_le_mul x (γ t_star)
    rw [hVz, Real.dist_eq, sub_zero, abs_of_nonneg (hV0 x), hd_γ] at hlip_z
    simp only [VC, hx, hy, ↓reduceIte, Real.dist_eq, sub_zero, abs_of_nonneg (hV0 x)]
    calc
      V x ≤ (L : ℝ) * (t_star * dist x y) := hlip_z
      _ ≤ (L : ℝ) * (1 * dist x y) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right ht_mem.1.2 dist_nonneg) L.coe_nonneg
      _ = (L : ℝ) * dist x y := by ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ C₁
  · by_cases hy : y ∈ C₁
    · simp only [hx, hy, ↓reduceIte]
      exact hV.dist_le_mul x y
    · exact hseg hx hy
  · by_cases hy : y ∈ C₁
    · rw [dist_comm, dist_comm x y]
      exact hseg hy hx
    · simp only [hx, hy, ↓reduceIte, dist_self]
      exact mul_nonneg L.coe_nonneg dist_nonneg

/-- **Connectedness of the positive phase `{x | 0 < V x}` under a uniform coarse cone (DS7)**:
If `V` is a physical translation limit of `zeroExtension g u` with `0 ∈ closure {x | 0 < V x}`
and `V 0 < 1`, and `g` satisfies `HasUniformBoundaryCoarseCone g e` (`‖e‖ = 1`), then
`{x | 0 < V x}` is preconnected. -/
theorem RigidityHypotheses.isPreconnected_positive_phase_of_coarse_cone
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hcone : HasUniformBoundaryCoarseCone g e)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hV_val : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hcl0 : (0 : Space (m + 1)) ∈ closure {x | 0 < V x}) (hV0_lt : V 0 < 1) :
    IsPreconnected {x | 0 < V x} := by
  let Ω_V : Set (Space (m + 1)) := {x | 0 < V x}
  have hΩ_open : IsOpen Ω_V := isOpen_lt continuous_const hV.continuous
  have hΩ_ne : Ω_V.Nonempty := closure_nonempty_iff.mp ⟨0, hcl0⟩
  obtain ⟨hV_lt_one, hΩ_ne_univ⟩ := hr.physical_translation_limit_lt_one_and_not_univ h hlim hV0_lt
  have hfront_ne : (frontier Ω_V).Nonempty := nonempty_frontier_iff.mpr ⟨hΩ_ne, hΩ_ne_univ⟩
  obtain ⟨p₀, hp₀_front⟩ := hfront_ne
  obtain ⟨R_cone, hR_cone, hV_cone⟩ :=
    hr.physical_translation_limit_coarse_cone h he hcone hV hV_val hlim
  -- Step 1: Truncated positive cone union `𝒱 ⊆ Ω_V` is nonempty and preconnected
  let C_cone : Set (Space (m + 1)) :=
    {w : Space (m + 1) | R_cone < ‖w‖ ∧ (1 / 4 : ℝ) * ‖w‖ < inner ℝ e w}
  let V_union : Set (Space (m + 1)) := ⋃ q ∈ frontier Ω_V, (fun w ↦ q + w) '' C_cone
  have hV_union_sub : V_union ⊆ Ω_V := by
    rintro x ⟨_, ⟨q, rfl⟩, _, ⟨hq_f, rfl⟩, w, hw, rfl⟩
    have hge := (hV_cone q hq_f w hw.1.le).1 hw.2.le
    change 0 < V (q + w)
    linarith
  -- Convex core `K_core ⊆ (p₀ + C_cone) ⊆ V_union`
  let K_core : Set (Space (m + 1)) :=
    {x : Space (m + 1) | R_cone < inner ℝ e (x - p₀) ∧ (1 / 4 : ℝ) * ‖x - p₀‖ < inner ℝ e (x - p₀)}
  have hK_core_conv : Convex ℝ K_core := by
    intro x hx y hy a b ha hb hab
    have hxy : a • x + b • y - p₀ = a • (x - p₀) + b • (y - p₀) := by
      calc
        a • x + b • y - p₀ = a • x + b • y - (a + b) • p₀ := by rw [hab, one_smul]
        _ = a • (x - p₀) + b • (y - p₀) := by module
    refine ⟨?_, ?_⟩
    · rw [hxy, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rcases lt_or_eq_of_le ha with ha_pos | rfl
      · have h1 : a * R_cone < a * inner ℝ e (x - p₀) := mul_lt_mul_of_pos_left hx.1 ha_pos
        have h2 : b * R_cone ≤ b * inner ℝ e (y - p₀) := mul_le_mul_of_nonneg_left hy.1.le hb
        nlinarith
      · rw [zero_add] at hab; subst hab
        simpa using hy.1
    · rw [hxy, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have hnorm_le : ‖a • (x - p₀) + b • (y - p₀)‖ ≤ a * ‖x - p₀‖ + b * ‖y - p₀‖ := by
        calc
          ‖a • (x - p₀) + b • (y - p₀)‖ ≤ ‖a • (x - p₀)‖ + ‖b • (y - p₀)‖ := norm_add_le _ _
          _ = a * ‖x - p₀‖ + b * ‖y - p₀‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      rcases lt_or_eq_of_le ha with ha_pos | rfl
      · have h1 : a * ((1 / 4 : ℝ) * ‖x - p₀‖) < a * inner ℝ e (x - p₀) :=
          mul_lt_mul_of_pos_left hx.2 ha_pos
        have h2 : b * ((1 / 4 : ℝ) * ‖y - p₀‖) ≤ b * inner ℝ e (y - p₀) :=
          mul_le_mul_of_nonneg_left hy.2.le hb
        linarith
      · rw [zero_add] at hab; subst hab
        simpa using hy.2
  have hK_core_ne : K_core.Nonempty := by
    refine ⟨p₀ + (R_cone + 1) • e, ?_, ?_⟩
    · have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
      change R_cone < inner ℝ e (p₀ + (R_cone + 1) • e - p₀)
      rw [add_sub_cancel_left, real_inner_smul_right, hee, mul_one]
      linarith
    · have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
      change (1 / 4 : ℝ) * ‖p₀ + (R_cone + 1) • e - p₀‖ < inner ℝ e (p₀ + (R_cone + 1) • e - p₀)
      rw [add_sub_cancel_left, real_inner_smul_right, hee, mul_one,
        norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity)]
      linarith
  have hK_core_sub : K_core ⊆ V_union := by
    intro x hx
    refine mem_iUnion₂.mpr ⟨p₀, hp₀_front, x - p₀, ⟨?_, hx.2⟩, add_sub_cancel p₀ x⟩
    have hle : inner ℝ e (x - p₀) ≤ ‖x - p₀‖ := by
      simpa only [he, one_mul] using real_inner_le_norm e (x - p₀)
    exact hx.1.trans_le hle
  have hV_union_pre : IsPreconnected V_union := by
    -- Express `V_union` as the union of `K_core` with rays `[0, T] • e` meeting `K_core`
    have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
    have hray_in {q w : Space (m + 1)} (hq : q ∈ frontier Ω_V) (hw : w ∈ C_cone) :
        ∃ S_ray : Set (Space (m + 1)), IsPreconnected S_ray ∧ q + w ∈ S_ray ∧
          S_ray ⊆ V_union ∧ (S_ray ∩ K_core).Nonempty := by
      let T : ℝ := R_cone + 4 * ‖q - p₀ + w‖ + 1
      have hT_pos : 0 < T := by dsimp only [T]; positivity
      let S_ray : Set (Space (m + 1)) := (fun t : ℝ ↦ (q + w) + t • e) '' Icc 0 T
      have hS_pre : IsPreconnected S_ray :=
        isPreconnected_Icc.image _ (by fun_prop : Continuous (fun t : ℝ ↦ (q + w) + t • e)).continuousOn
      have hqw_mem : q + w ∈ S_ray := ⟨0, ⟨le_rfl, hT_pos.le⟩, by simp⟩
      have hS_sub : S_ray ⊆ V_union := by
        rintro _ ⟨t, ht, rfl⟩
        refine mem_iUnion₂.mpr ⟨q, hq, w + t • e, ⟨?_, ?_⟩, (add_assoc q w (t • e)).symm⟩
        · have hsq : R_cone ^ 2 < ‖w + t • e‖ ^ 2 := by
            rw [← real_inner_self_eq_norm_sq]
            simp only [inner_add_left, inner_add_right, real_inner_smul_left,
              real_inner_smul_right, real_inner_self_eq_norm_sq]
            simp_rw [real_inner_comm e w]
            have hw_in_pos : 0 < inner ℝ e w :=
              (mul_pos (by norm_num) (hR_cone.trans hw.1)).trans hw.2
            have hw_sq : R_cone ^ 2 < ‖w‖ ^ 2 := pow_lt_pow_left₀ hw.1 hR_cone.le (by norm_num)
            have hte_nn : 0 ≤ ‖t • e‖ ^ 2 := sq_nonneg _
            have htw_nn : 0 ≤ t * inner ℝ e w := mul_nonneg ht.1 hw_in_pos.le
            linarith only [hw_sq, htw_nn, hte_nn]
          exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq
        · have hnorm_le : ‖w + t • e‖ ≤ ‖w‖ + t := by
            calc
              ‖w + t • e‖ ≤ ‖w‖ + ‖t • e‖ := norm_add_le _ _
              _ = ‖w‖ + t := by rw [norm_smul, he, mul_one, Real.norm_of_nonneg ht.1]
          rw [inner_add_right, real_inner_smul_right, hee, mul_one]
          linarith [hw.2, ht.1]
      have hT_K : (q + w) + T • e ∈ K_core := by
        let u_vec : Space (m + 1) := q - p₀ + w
        have heq_sub : (q + w) + T • e - p₀ = u_vec + T • e := by dsimp only [u_vec]; abel
        have hu_in : -‖u_vec‖ ≤ inner ℝ e u_vec := by
          have hn : inner ℝ e (-u_vec) ≤ ‖u_vec‖ := by
            simpa only [he, one_mul, norm_neg] using real_inner_le_norm e (-u_vec)
          rw [inner_neg_right] at hn; linarith
        have hnorm_le : ‖u_vec + T • e‖ ≤ ‖u_vec‖ + T := by
          calc
            ‖u_vec + T • e‖ ≤ ‖u_vec‖ + ‖T • e‖ := norm_add_le _ _
            _ = ‖u_vec‖ + T := by rw [norm_smul, he, mul_one, Real.norm_of_nonneg hT_pos.le]
        refine ⟨?_, ?_⟩
        · rw [heq_sub, inner_add_right, real_inner_smul_right, hee, mul_one]
          dsimp only [T]
          linarith [norm_nonneg u_vec]
        · rw [heq_sub, inner_add_right, real_inner_smul_right, hee, mul_one]
          dsimp only [T] at hnorm_le ⊢
          linarith [norm_nonneg u_vec]
      exact ⟨S_ray, hS_pre, hqw_mem, hS_sub, ⟨(q + w) + T • e, ⟨T, ⟨hT_pos.le, le_rfl⟩, rfl⟩, hT_K⟩⟩
    intro U₁ U₂ hU₁ hU₂ hcov hne₁ hne₂
    -- `K_core ⊆ V_union ⊆ U₁ ∪ U₂` is convex (hence preconnected)
    have hK_cov : K_core ⊆ U₁ ∪ U₂ := hK_core_sub.trans hcov
    -- Any point of `V_union ∩ Uᵢ` forces `K_core ∩ Uᵢ` nonempty via `S_ray ∪ K_core`
    have hK_meets {U_a U_b : Set (Space (m + 1))} (hUa : IsOpen U_a) (hUb : IsOpen U_b)
        (hc_ab : V_union ⊆ U_a ∪ U_b) (hne_a : (V_union ∩ U_a).Nonempty)
        (hdisj_K : K_core ∩ (U_a ∩ U_b) = ∅)
        (hdisj_V : V_union ∩ (U_a ∩ U_b) = ∅) : (K_core ∩ U_a).Nonempty := by
      obtain ⟨x, hxV, hxUa⟩ := hne_a
      rcases mem_iUnion₂.mp hxV with ⟨q, hq, w, hw, rfl⟩
      obtain ⟨S_ray, hS_pre, hqw_S, hS_sub, hSK_ne⟩ := hray_in hq hw
      have hSK_pre : IsPreconnected (S_ray ∪ K_core) :=
        hS_pre.union' hSK_ne hK_core_conv.isPreconnected
      by_contra hK_not_a
      rw [not_nonempty_iff_eq_empty] at hK_not_a
      have hK_in_b : K_core ⊆ U_b := by
        intro z hz
        rcases hc_ab (hK_core_sub hz) with hza | hzb
        · exfalso
          have hm : z ∈ K_core ∩ U_a := ⟨hz, hza⟩
          rw [hK_not_a] at hm
          exact notMem_empty z hm
        · exact hzb
      obtain ⟨z₀, hz₀⟩ := hK_core_ne
      have hSK_sub : S_ray ∪ K_core ⊆ V_union := union_subset hS_sub hK_core_sub
      have hSK_inter : ((S_ray ∪ K_core) ∩ (U_a ∩ U_b)).Nonempty :=
        hSK_pre U_a U_b hUa hUb (hSK_sub.trans hc_ab)
          ⟨q + w, Or.inl hqw_S, hxUa⟩ ⟨z₀, Or.inr hz₀, hK_in_b hz₀⟩
      obtain ⟨y, hySK, hyab⟩ := hSK_inter
      have hyV : y ∈ V_union ∩ (U_a ∩ U_b) := ⟨hSK_sub hySK, hyab⟩
      rw [hdisj_V] at hyV
      exact notMem_empty y hyV
    by_contra hdisj_empty
    rw [not_nonempty_iff_eq_empty] at hdisj_empty
    have hdisj_K : K_core ∩ (U₁ ∩ U₂) = ∅ :=
      subset_eq_empty (inter_subset_inter_left _ hK_core_sub) hdisj_empty
    have hK1 := hK_meets hU₁ hU₂ hcov hne₁ hdisj_K hdisj_empty
    have hcov_symm : V_union ⊆ U₂ ∪ U₁ := by rwa [union_comm]
    have hdisj_symm : V_union ∩ (U₂ ∩ U₁) = ∅ := by rwa [inter_comm U₂ U₁]
    have hdisj_K_symm : K_core ∩ (U₂ ∩ U₁) = ∅ := by rwa [inter_comm U₂ U₁]
    have hK2 := hK_meets hU₂ hU₁ hcov_symm hne₂ hdisj_K_symm hdisj_symm
    obtain ⟨z, hzK, hzab⟩ := hK_core_conv.isPreconnected U₁ U₂ hU₁ hU₂ hK_cov hK1 hK2
    have hzV : z ∈ V_union ∩ (U₁ ∩ U₂) := ⟨hK_core_sub hzK, hzab⟩
    rw [hdisj_empty] at hzV
    exact notMem_empty z hzV
  -- Step 2: Every `x ∈ Ω_V \ V_union` satisfies `infDist x Ω_Vᶜ ≤ 4 * R_cone`
  have hdist_le_of_notMem {x : Space (m + 1)} (hx : x ∈ Ω_V) (hx_not : x ∉ V_union) :
      Metric.infDist x Ω_Vᶜ ≤ 4 * R_cone := by
    by_contra hgt_D
    push Not at hgt_D
    let D : ℝ := Metric.infDist x Ω_Vᶜ
    have hD_gt : 4 * R_cone < D := hgt_D
    have hD_pos : 0 < D := by linarith
    obtain ⟨q, hq_front, hDq⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hΩ_ne_univ
    have hnorm_xq : ‖x - q‖ = D := by rw [← dist_eq_norm, ← hDq]
    have hnot_cone : inner ℝ e (x - q) ≤ (1 / 4 : ℝ) * ‖x - q‖ := by
      by_contra hin
      push Not at hin
      apply hx_not
      refine mem_iUnion₂.mpr ⟨q, hq_front, x - q, ⟨?_, hin⟩, add_sub_cancel q x⟩
      rw [hnorm_xq]
      linarith
    let z : Space (m + 1) := D⁻¹ • (x - q)
    have hz_norm : ‖z‖ = 1 := by
      simp only [z, norm_smul, hnorm_xq, Real.norm_of_nonneg (inv_nonneg.mpr hD_pos.le),
        inv_mul_cancel₀ hD_pos.ne']
    have hx_eq : x - q = D • z := by simp [z, smul_smul, hD_pos.ne']
    have hez_le : inner ℝ e z ≤ 1 / 4 := by
      rw [hx_eq, real_inner_smul_right, norm_smul, hz_norm, mul_one,
        Real.norm_of_nonneg hD_pos.le] at hnot_cone
      exact le_of_mul_le_mul_left (by linarith only [hnot_cone] : D * inner ℝ e z ≤ D * (1 / 4)) hD_pos
    have hez_ge : -1 ≤ inner ℝ e z := by
      have hn : inner ℝ e (-z) ≤ 1 := by
        simpa only [he, hz_norm, one_mul, norm_neg] using real_inner_le_norm e (-z)
      rw [inner_neg_right] at hn
      linarith
    have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
    have hzz : inner ℝ z z = 1 := by rw [real_inner_self_eq_norm_sq, hz_norm]; norm_num
    let u_vec : Space (m + 1) := z - (2 : ℝ) • e
    have hu_sq : ‖u_vec‖ ^ 2 = 5 - 4 * inner ℝ e z := by
      rw [← real_inner_self_eq_norm_sq]
      change inner ℝ (z - (2 : ℝ) • e) (z - (2 : ℝ) • e) = 5 - 4 * inner ℝ e z
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        hee, hzz]
      rw [real_inner_comm z e]
      ring
    have hu_ge2 : 2 ≤ ‖u_vec‖ := by
      have hsq : (2 : ℝ) ^ 2 ≤ ‖u_vec‖ ^ 2 := by rw [hu_sq]; linarith
      exact le_of_sq_le_sq hsq (norm_nonneg _)
    have hu_le3 : ‖u_vec‖ ≤ 3 := by
      have hsq : ‖u_vec‖ ^ 2 ≤ (3 : ℝ) ^ 2 := by rw [hu_sq]; linarith
      exact le_of_sq_le_sq hsq (by norm_num)
    have hu_pos : 0 < ‖u_vec‖ := by linarith
    let v : Space (m + 1) := ‖u_vec‖⁻¹ • u_vec
    have hv_norm : ‖v‖ = 1 := by
      simp only [v, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hu_pos.le),
        inv_mul_cancel₀ hu_pos.ne']
    have hev_le : inner ℝ e v ≤ -(1 / 4 : ℝ) := by
      have heu : inner ℝ e u_vec ≤ -(7 / 4 : ℝ) := by
        have h2e : inner ℝ e ((2 : ℝ) • e) = 2 * inner ℝ e e := real_inner_smul_right _ _ _
        change inner ℝ e (z - (2 : ℝ) • e) ≤ -(7 / 4 : ℝ)
        rw [inner_sub_right, h2e, hee]
        linarith only [hez_le]
      have hmul : inner ℝ e u_vec ≤ -(1 / 4 : ℝ) * ‖u_vec‖ := by linarith only [heu, hu_le3]
      change inner ℝ e (‖u_vec‖⁻¹ • u_vec) ≤ -(1 / 4 : ℝ)
      rw [real_inner_smul_right]
      have h1 := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hu_pos.le)
      have h2 : ‖u_vec‖⁻¹ * (-(1 / 4 : ℝ) * ‖u_vec‖) = -(1 / 4 : ℝ) := by
        field_simp [hu_pos.ne']
      linarith only [h1, h2]
    have hzv_ge : (1 / 6 : ℝ) ≤ inner ℝ z v := by
      have hzu : (1 / 2 : ℝ) ≤ inner ℝ z u_vec := by
        have h2ze : inner ℝ z ((2 : ℝ) • e) = 2 * inner ℝ z e := real_inner_smul_right _ _ _
        change (1 / 2 : ℝ) ≤ inner ℝ z (z - (2 : ℝ) • e)
        rw [inner_sub_right, h2ze, hzz, real_inner_comm e z]
        linarith only [hez_le]
      have hmul : (1 / 6 : ℝ) * ‖u_vec‖ ≤ inner ℝ z u_vec := by linarith only [hzu, hu_le3]
      change (1 / 6 : ℝ) ≤ inner ℝ z (‖u_vec‖⁻¹ • u_vec)
      rw [real_inner_smul_right]
      have h1 := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hu_pos.le)
      have h2 : ‖u_vec‖⁻¹ * ((1 / 6 : ℝ) * ‖u_vec‖) = (1 / 6 : ℝ) := by
        field_simp [hu_pos.ne']
      linarith only [h1, h2]
    -- Test `y_pt := q + (D / 4) • v` in the negative coarse cone of `q`
    let w_neg : Space (m + 1) := (D / 4) • v
    have hw_neg_norm : ‖w_neg‖ = D / 4 := by
      dsimp only [w_neg]
      rw [norm_smul, hv_norm, mul_one,
        Real.norm_of_nonneg (div_nonneg hD_pos.le (by norm_num : (0 : ℝ) ≤ 4))]
    have hw_neg_ge : R_cone ≤ ‖w_neg‖ := by rw [hw_neg_norm]; linarith only [hD_gt]
    have hw_neg_in : inner ℝ e w_neg ≤ -(1 / 4 : ℝ) * ‖w_neg‖ := by
      change inner ℝ e ((D / 4) • v) ≤ -(1 / 4 : ℝ) * ‖w_neg‖
      rw [real_inner_smul_right, hw_neg_norm]
      have hm := mul_le_mul_of_nonneg_left hev_le (div_nonneg hD_pos.le (by norm_num : (0 : ℝ) ≤ 4))
      linarith only [hm]
    have hVy0 : V (q + w_neg) = 0 := (hV_cone q hq_front w_neg hw_neg_ge).2 hw_neg_in
    have hy_compl : q + w_neg ∈ Ω_Vᶜ := by
      change ¬ 0 < V (q + w_neg)
      rw [hVy0]; exact lt_irrefl 0
    have hdist_ge : D ≤ dist x (q + w_neg) := Metric.infDist_le_dist_of_mem hy_compl
    have hdist_sq_lt : dist x (q + w_neg) ^ 2 < D ^ 2 := by
      rw [dist_eq_norm]
      have heq_d : x - (q + w_neg) = D • (z - (1 / 4 : ℝ) • v) := by
        change x - (q + (D / 4) • v) = D • (z - (1 / 4 : ℝ) • v)
        rw [← sub_sub, hx_eq]
        module
      rw [heq_d, norm_smul, Real.norm_of_nonneg hD_pos.le, mul_pow]
      have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv_norm]; norm_num
      have hunit_sq : ‖z - (1 / 4 : ℝ) • v‖ ^ 2 < 1 := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
          hzz, hvv]
        simp_rw [real_inner_comm z v]
        linarith only [hzv_ge]
      exact mul_lt_of_lt_one_right (sq_pos_of_pos hD_pos) hunit_sq
    have hlt_D : dist x (q + w_neg) < D := lt_of_pow_lt_pow_left₀ 2 hD_pos.le hdist_sq_lt
    linarith
  -- Step 3: Exclude any nonempty open clopen piece `C₁ ⊆ Ω_V` disjoint from `V_union`
  have hexclude_piece {C₁ : Set (Space (m + 1))} (hC₁_open : IsOpen C₁)
      (hC₁_sub : C₁ ⊆ Ω_V) (hC₂_open : IsOpen (Ω_V \ C₁))
      (hC₁_ne : C₁.Nonempty) (hdisj_V : Disjoint C₁ V_union) : False := by
    have hfront_C₁_zero : ∀ z ∈ frontier C₁, V z = 0 := by
      intro z hz
      by_contra hVz_ne
      have hz_pos : z ∈ Ω_V := lt_of_le_of_ne (hV_val z).1 (Ne.symm hVz_ne)
      have hz_not_C₁ : z ∉ C₁ := by
        rw [frontier, hC₁_open.interior_eq] at hz
        exact hz.2
      have hz_C₂ : z ∈ Ω_V \ C₁ := ⟨hz_pos, hz_not_C₁⟩
      obtain ⟨y, hy_C₂, hy_C₁⟩ := mem_closure_iff.mp hz.1 (Ω_V \ C₁) hC₂_open hz_C₂
      exact hy_C₂.2 hy_C₁
    obtain ⟨L_mod, hL_mod, hexp_mod⟩ := hr.exists_equilibrium_distance_exp_bound h
    let b_star : ℝ := 1 - Real.exp (-L_mod * (4 * R_cone + 1))
    have hb_star_lt : b_star < 1 := by
      dsimp only [b_star]
      linarith [Real.exp_pos (-L_mod * (4 * R_cone + 1))]
    have hV_le_b_star : ∀ x ∈ C₁, V x ≤ b_star := by
      intro x hx
      have hx_not_V : x ∉ V_union := disjoint_left.mp hdisj_V hx
      have hd_le := hdist_le_of_notMem (hC₁_sub hx) hx_not_V
      have hc_ne : Ω_Vᶜ.Nonempty := nonempty_compl.mpr hΩ_ne_univ
      have hlt_inf : Metric.infDist x Ω_Vᶜ < 4 * R_cone + 1 := by linarith
      obtain ⟨y₀, hy₀_c, hdy₀⟩ := (Metric.infDist_lt_iff hc_ne).mp hlt_inf
      have hVy₀ : V y₀ = 0 := le_antisymm (not_lt.mp hy₀_c) (hV_val y₀).1
      have hexp_xy := hexp_mod p V hlim y₀ x
      rw [hVy₀, sub_zero, one_mul] at hexp_xy
      have hexp_mono : Real.exp (-L_mod * (4 * R_cone + 1)) ≤ Real.exp (-L_mod * dist x y₀) :=
        Real.exp_le_exp.mpr (by nlinarith)
      dsimp only [b_star]
      linarith
    -- Lower potential bound `w_min > 0` on `[0, b_star]` and upper potential bound `W_max`
    obtain ⟨c_W, C_W, hc_W, _, hW_comp⟩ := hr.potential_quadratic_comparison h
    let w_min : ℝ := c_W * (1 - b_star) ^ 2
    have hw_min_pos : 0 < w_min := mul_pos hc_W (sq_pos_of_pos (sub_pos.mpr hb_star_lt))
    obtain ⟨MW, hMW⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      h.normalizedPotential_continuousOn
    let W_max : ℝ := |MW| + 1
    have hW_max_pos : 0 < W_max := by dsimp only [W_max]; positivity
    have hW_upper (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : normalizedPotential f s ≤ W_max := by
      dsimp only [W_max]
      linarith [(le_abs_self _).trans ((hMW s hs).trans (le_abs_self MW))]
    have hW_lower_C₁ {x : Space (m + 1)} (hx : x ∈ C₁) : w_min ≤ normalizedPotential f (V x) := by
      have hlo := (hW_comp (V x) (hV_val x)).1
      have h1 : 1 - b_star ≤ 1 - V x := by linarith [hV_le_b_star x hx]
      have hsq : (1 - b_star) ^ 2 ≤ (1 - V x) ^ 2 :=
        pow_le_pow_left₀ (sub_pos.mpr hb_star_lt).le h1 2
      dsimp only [w_min]
      exact (mul_le_mul_of_nonneg_left hsq hc_W.le).trans hlo
    -- Energy recurrence `I(r + 1) ≤ C_shell * (I(r + 1) - I(r))` for all `r ≥ 1`
    classical
    let VC : Space (m + 1) → ℝ := fun x ↦ if x ∈ C₁ then V x else 0
    have hVC_lip : LipschitzWith ⟨κ, h.kappa_pos.le⟩ VC :=
      lipschitzWith_piece_of_frontier_zero hV (fun y ↦ (hV_val y).1) hC₁_open hfront_C₁_zero
    let I_en : ℝ → ℝ := fun r ↦ ∫ x in C₁ ∩ closedBall 0 r, phaseEnergyDensity f 0 V x
    let C_shell : ℝ := 2 + (1 + W_max) / w_min
    have hC_shell_gt1 : 1 < C_shell := by
      have hpos_div : 0 < (1 + W_max) / w_min := div_pos (by positivity) hw_min_pos
      dsimp only [C_shell]; linarith
    have hrec (r : ℝ) (hr1 : 1 ≤ r) :
        I_en (r + 1) ≤ C_shell * (I_en (r + 1) - I_en r) := by
      let θ_r : Space (m + 1) → ℝ := fun x ↦ min 1 (max 0 (‖x‖ - r))
      have hθ_lip : LipschitzWith 1 θ_r := (radialRamp_lipschitz (m + 1) r).const_min 1
      have hθ_val (x : Space (m + 1)) : θ_r x ∈ Icc (0 : ℝ) 1 :=
        ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
      let Zr : Space (m + 1) → ℝ := fun x ↦ V x - (1 - θ_r x) * VC x
      have hZr_lip : LocallyLipschitz Zr :=
        hV.locallyLipschitz.sub
          (locallyLipschitz_mul_real
            (((contDiff_const (c := (1 : ℝ)) : ContDiff ℝ 1 _).locallyLipschitz).sub
              hθ_lip.locallyLipschitz)
            hVC_lip.locallyLipschitz)
      have hZr_eq (x : Space (m + 1)) : Zr x = if x ∈ C₁ then θ_r x * V x else V x := by
        dsimp only [Zr, VC]
        split_ifs <;> ring
      have hZr_val (x : Space (m + 1)) : Zr x ∈ Icc (0 : ℝ) 1 := by
        rw [hZr_eq]
        split_ifs with hx
        · exact ⟨mul_nonneg (hθ_val x).1 (hV_val x).1,
            (mul_le_of_le_one_left (hV_val x).1 (hθ_val x).2).trans (hV_val x).2⟩
        · exact hV_val x
      have hZr_le_V (x : Space (m + 1)) : Zr x ≤ V x := by
        rw [hZr_eq]
        split_ifs with hx
        · exact mul_le_of_le_one_left (hV_val x).1 (hθ_val x).2
        · exact le_rfl
      have hZr_supp : tsupport (fun x ↦ Zr x - V x) ⊆ closedBall 0 (r + 1) := by
        apply closure_minimal _ isClosed_closedBall
        intro x hx
        rw [Function.mem_support] at hx
        by_contra hnot
        have hgt : r + 1 < ‖x‖ := by
          simpa only [mem_closedBall, dist_zero_right, not_le] using hnot
        have hθ1 : θ_r x = 1 := min_eq_left (le_trans (by linarith) (le_max_right _ _))
        exact hx (by dsimp only [Zr]; rw [hθ1]; ring)
      have hmin_Zr := hr.physical_translation_limit_energy_minimal h (by linarith : 0 ≤ r + 1)
        hV hV_val hlim hZr_lip hZr_val hZr_supp
      let K_big := closedBall (0 : Space (m + 1)) (r + 1 + 2)
      have hK_big : IsCompact K_big := isCompact_closedBall _ _
      have hiV_K := h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hV_val 0 hK_big
      have hiZ_K := h.integrableOn_lipschitz_phaseEnergy hZr_lip hZr_val 0 hK_big
      -- Decompose `K_big` into `C₁ ∩ K_big` and `K_big \ C₁`
      have hsplit_C₁ (G : Space (m + 1) → ℝ) (hi : IntegrableOn G K_big) :
          (∫ x in K_big, G x) = (∫ x in K_big ∩ C₁, G x) + ∫ x in K_big \ C₁, G x :=
        (integral_inter_add_sdiff hC₁_open.measurableSet hi).symm
      -- On `K_big \ C₁`, `phaseEnergyDensity f 0 Zr = phaseEnergyDensity f 0 V` everywhere
      have heq_off_C₁ : (∫ x in K_big \ C₁, phaseEnergyDensity f 0 Zr x) =
          ∫ x in K_big \ C₁, phaseEnergyDensity f 0 V x := by
        apply setIntegral_congr_fun (isClosed_closedBall.measurableSet.diff hC₁_open.measurableSet)
        intro x hx
        by_cases hpV : 0 < V x
        · have hx_C₂ : x ∈ Ω_V \ C₁ := ⟨hpV, hx.2⟩
          have hev : Zr =ᶠ[𝓝 x] V := by
            filter_upwards [hC₂_open.mem_nhds hx_C₂] with y hy
            rw [hZr_eq]
            simp only [hy.2, ↓reduceIte]
          have hxy : Zr x = V x := hev.eq_of_nhds
          have hpZ : 0 < Zr x := by rwa [hxy]
          rw [phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hZr_val y).1),
            phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hV_val y).1),
            hev.gradient_eq]
          rw [indicator_of_mem (s := {y | 0 < Zr y}) hpZ,
            indicator_of_mem (s := {y | 0 < V y}) hpV, hxy]
        · have hV0x : V x = 0 := le_antisymm (not_lt.mp hpV) (hV_val x).1
          have hZ0x : Zr x = 0 := le_antisymm ((hZr_le_V x).trans_eq hV0x) (hZr_val x).1
          have hpZ : ¬ 0 < Zr x := by rw [hZ0x]; exact lt_irrefl 0
          simp only [phaseEnergyDensity, indicator_of_notMem (s := {y | 0 < Zr y}) hpZ,
            indicator_of_notMem (s := {y | 0 < V y}) hpV]
      -- Further split `K_big ∩ C₁ = (C₁ ∩ closedBall 0 (r + 1)) ∪ ((K_big ∩ C₁) \ closedBall 0 (r + 1))`
      have hcb_r1_sub : C₁ ∩ closedBall 0 (r + 1) ⊆ K_big ∩ C₁ := by
        intro x hx
        exact ⟨closedBall_subset_closedBall (by linarith) hx.2, hx.1⟩
      have hsplit_r1 (G : Space (m + 1) → ℝ) (hi : IntegrableOn G (K_big ∩ C₁)) :
          (∫ x in K_big ∩ C₁, G x) =
            (∫ x in C₁ ∩ closedBall 0 (r + 1), G x) +
              ∫ x in (K_big ∩ C₁) \ closedBall 0 (r + 1), G x := by
        have he := integral_inter_add_sdiff
          (isClosed_closedBall (x := (0 : Space (m + 1))) (ε := r + 1)).measurableSet hi
        have hinter : (K_big ∩ C₁) ∩ closedBall 0 (r + 1) = C₁ ∩ closedBall 0 (r + 1) := by
          ext x
          simp only [mem_inter_iff, K_big]
          exact ⟨fun ⟨⟨_, h2⟩, h3⟩ ↦ ⟨h2, h3⟩,
            fun ⟨h1, h2⟩ ↦ ⟨⟨closedBall_subset_closedBall (by linarith) h2, h1⟩, h2⟩⟩
        rw [hinter] at he
        exact he.symm
      -- Almost everywhere on `(K_big ∩ C₁) \ closedBall 0 (r + 1)`, `e(Zr) = e(V)`
      have heq_outer : (∫ x in (K_big ∩ C₁) \ closedBall 0 (r + 1), phaseEnergyDensity f 0 Zr x) =
          ∫ x in (K_big ∩ C₁) \ closedBall 0 (r + 1), phaseEnergyDensity f 0 V x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem
            ((isClosed_closedBall.measurableSet.inter hC₁_open.measurableSet).diff
              isClosed_closedBall.measurableSet),
          ae_restrict_of_ae (ae_differentiableAt_of_locallyLipschitz hZr_lip),
          ae_restrict_of_ae (ae_differentiableAt_of_locallyLipschitz hV.locallyLipschitz)]
            with x hx hdZ hdV
        have hgt : r + 1 < ‖x‖ := by
          simpa only [mem_closedBall, dist_zero_right, not_le] using hx.2
        have hθ1 : θ_r x = 1 := min_eq_left (le_trans (by linarith) (le_max_right _ _))
        have hZV_x : Zr x = V x := by dsimp only [Zr]; rw [hθ1]; ring
        have hmin_diff : IsLocalMin (fun y ↦ V y - Zr y) x := by
          filter_upwards with y
          rw [hZV_x, sub_self]
          exact sub_nonneg.mpr (hZr_le_V y)
        have hfderiv0 := hmin_diff.fderiv_eq_zero
        have hsub_fd : fderiv ℝ (fun y ↦ V y - Zr y) x = fderiv ℝ V x - fderiv ℝ Zr x :=
          (hdV.hasFDerivAt.sub hdZ.hasFDerivAt).fderiv
        rw [hsub_fd] at hfderiv0
        have hg_eq : gradient Zr x = gradient V x := by
          simp only [gradient, sub_eq_zero.mp hfderiv0]
        rw [phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hZr_val y).1),
          phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hV_val y).1), hg_eq]
        have hpV : 0 < V x := hC₁_sub hx.1.2
        have hpZ : 0 < Zr x := by rwa [hZV_x]
        rw [indicator_of_mem (s := {y | 0 < Zr y}) hpZ,
          indicator_of_mem (s := {y | 0 < V y}) hpV, hZV_x]
      -- On `C₁ ∩ closedBall 0 r`, `Zr = 0`, so `e(Zr) = 0`; on the shell, `e(Zr) ≤ C_shell * e(V)`
      have hsplit_r (G : Space (m + 1) → ℝ)
          (hi : IntegrableOn G (C₁ ∩ closedBall 0 (r + 1))) :
          (∫ x in C₁ ∩ closedBall 0 (r + 1), G x) =
            (∫ x in C₁ ∩ closedBall 0 r, G x) +
              ∫ x in (C₁ ∩ closedBall 0 (r + 1)) \ closedBall 0 r, G x := by
        have he := integral_inter_add_sdiff
          (isClosed_closedBall (x := (0 : Space (m + 1))) (ε := r)).measurableSet hi
        have hinter : (C₁ ∩ closedBall 0 (r + 1)) ∩ closedBall 0 r = C₁ ∩ closedBall 0 r := by
          ext x
          simp only [mem_inter_iff]
          exact ⟨fun ⟨⟨h1, _⟩, h3⟩ ↦ ⟨h1, h3⟩,
            fun ⟨h1, h2⟩ ↦ ⟨⟨h1, closedBall_subset_closedBall (by linarith) h2⟩, h2⟩⟩
        rw [hinter] at he
        exact he.symm
      have hz_in : (∫ x in C₁ ∩ closedBall 0 r, phaseEnergyDensity f 0 Zr x) = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro x hx
        have hnx : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx.2
        have hθ0 : θ_r x = 0 := by
          dsimp only [θ_r]
          rw [max_eq_left (sub_nonpos.mpr hnx), min_eq_right zero_le_one]
        have hZ0 : Zr x = 0 := by rw [hZr_eq]; simp only [hx.1, ↓reduceIte, hθ0, zero_mul]
        simp only [phaseEnergyDensity, indicator_apply, mem_ofPred_eq, hZ0,
          lt_self_iff_false, ↓reduceIte]
      have hshell_bound :
          (∫ x in (C₁ ∩ closedBall 0 (r + 1)) \ closedBall 0 r, phaseEnergyDensity f 0 Zr x) ≤
            C_shell * ∫ x in (C₁ ∩ closedBall 0 (r + 1)) \ closedBall 0 r,
              phaseEnergyDensity f 0 V x := by
        let Sh := (C₁ ∩ closedBall 0 (r + 1)) \ closedBall 0 r
        have hSh_sub : Sh ⊆ K_big := fun x hx ↦
          closedBall_subset_closedBall (by linarith) hx.1.2
        rw [← integral_const_mul]
        apply integral_mono_ae (hiZ_K.mono_set hSh_sub) ((hiV_K.mono_set hSh_sub).const_mul C_shell)
        filter_upwards [ae_restrict_mem
            ((hC₁_open.measurableSet.inter isClosed_closedBall.measurableSet).diff
              isClosed_closedBall.measurableSet),
          ae_restrict_of_ae (ae_differentiableAt_of_locallyLipschitz hθ_lip.locallyLipschitz),
          ae_restrict_of_ae (ae_differentiableAt_of_locallyLipschitz hV.locallyLipschitz)]
            with x hx hdθ hdV
        have hxC₁ : x ∈ C₁ := hx.1.1
        have hpV : 0 < V x := hC₁_sub hxC₁
        have hev_prod : Zr =ᶠ[𝓝 x] fun y ↦ θ_r y * V y := by
          filter_upwards [hC₁_open.mem_nhds hxC₁] with y hy
          rw [hZr_eq]
          simp only [hy, ↓reduceIte]
        have hg_prod : gradient Zr x = θ_r x • gradient V x + V x • gradient θ_r x := by
          rw [hev_prod.gradient_eq]
          have hfd : fderiv ℝ (fun y ↦ θ_r y * V y) x =
              θ_r x • fderiv ℝ V x + V x • fderiv ℝ θ_r x :=
            (hdθ.hasFDerivAt.mul hdV.hasFDerivAt).fderiv
          rw [gradient, gradient, gradient, hfd, map_add, map_smul, map_smul]
        have hgθ_le : ‖gradient θ_r x‖ ≤ 1 := by
          rw [gradient, LinearIsometryEquiv.norm_map]
          simpa using norm_fderiv_le_of_lipschitz ℝ hθ_lip (x₀ := x)
        have hgZ_sq : ‖gradient Zr x‖ ^ 2 / 2 ≤ ‖gradient V x‖ ^ 2 + V x ^ 2 := by
          have htri : ‖gradient Zr x‖ ≤ ‖gradient V x‖ + V x := by
            rw [hg_prod]
            calc
              ‖θ_r x • gradient V x + V x • gradient θ_r x‖
                ≤ ‖θ_r x • gradient V x‖ + ‖V x • gradient θ_r x‖ := norm_add_le _ _
              _ = θ_r x * ‖gradient V x‖ + V x * ‖gradient θ_r x‖ := by
                rw [norm_smul, norm_smul, Real.norm_of_nonneg (hθ_val x).1,
                  Real.norm_of_nonneg (hV_val x).1]
              _ ≤ 1 * ‖gradient V x‖ + V x * 1 :=
                add_le_add (mul_le_mul_of_nonneg_right (hθ_val x).2 (norm_nonneg _))
                  (mul_le_mul_of_nonneg_left hgθ_le (hV_val x).1)
              _ = ‖gradient V x‖ + V x := by ring
          have hsq : ‖gradient Zr x‖ ^ 2 ≤ (‖gradient V x‖ + V x) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) htri 2
          have hdiff_nn : 0 ≤ (‖gradient V x‖ - V x) ^ 2 := sq_nonneg _
          have hid_sq : 2 * (‖gradient V x‖ ^ 2 + V x ^ 2) -
              (‖gradient V x‖ + V x) ^ 2 = (‖gradient V x‖ - V x) ^ 2 := by ring
          linarith only [hsq, hdiff_nn, hid_sq]
        have hpot_Z_le : {y | 0 < Zr y}.indicator (fun y ↦ normalizedPotential f (Zr y)) x ≤
            W_max := by
          by_cases hpZ : 0 < Zr x
          · rw [indicator_of_mem (s := {y | 0 < Zr y}) hpZ]
            exact hW_upper (Zr x) (hZr_val x)
          · rw [indicator_of_notMem (s := {y | 0 < Zr y}) hpZ]
            exact hW_max_pos.le
        have hW_lo := hW_lower_C₁ hxC₁
        have hVx_sq_le : V x ^ 2 ≤ 1 := pow_le_one₀ (hV_val x).1 (hV_val x).2
        have heZ := phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hZr_val y).1) f x
        have heV : phaseEnergyDensity f 0 V x =
            ‖gradient V x‖ ^ 2 / 2 + normalizedPotential f (V x) := by
          rw [phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hV_val y).1),
            indicator_of_mem (s := {y | 0 < V y}) hpV]
        change phaseEnergyDensity f 0 Zr x ≤ C_shell * phaseEnergyDensity f 0 V x
        rw [heZ, heV]
        have hRw_nn : 0 ≤ (1 + W_max) / w_min :=
          div_nonneg (by linarith only [hW_max_pos]) hw_min_pos.le
        have hdiv_le : 1 + W_max ≤ ((1 + W_max) / w_min) * normalizedPotential f (V x) := by
          calc
            1 + W_max = ((1 + W_max) / w_min) * w_min := by field_simp [hw_min_pos.ne']
            _ ≤ ((1 + W_max) / w_min) * normalizedPotential f (V x) :=
              mul_le_mul_of_nonneg_left hW_lo hRw_nn
        have hPV_nn := hr.normalizedPotential_nonneg h (hV_val x)
        have hRw_kin_nn : 0 ≤ ((1 + W_max) / w_min) * (‖gradient V x‖ ^ 2 / 2) :=
          mul_nonneg hRw_nn (by positivity)
        have hexpand : C_shell * (‖gradient V x‖ ^ 2 / 2 + normalizedPotential f (V x)) =
            ‖gradient V x‖ ^ 2 + 2 * normalizedPotential f (V x) +
              ((1 + W_max) / w_min) * (‖gradient V x‖ ^ 2 / 2) +
              ((1 + W_max) / w_min) * normalizedPotential f (V x) := by
          dsimp only [C_shell]; ring
        linarith only [hgZ_sq, hVx_sq_le, hpot_Z_le, hdiv_le, hPV_nn, hRw_kin_nn, hexpand]
      -- Assemble integral cancellations on `K_big`
      have hV_d1 := hsplit_C₁ (phaseEnergyDensity f 0 V) hiV_K
      have hZ_d1 := hsplit_C₁ (phaseEnergyDensity f 0 Zr) hiZ_K
      have hV_d2 := hsplit_r1 (phaseEnergyDensity f 0 V) (hiV_K.mono_set inter_subset_left)
      have hZ_d2 := hsplit_r1 (phaseEnergyDensity f 0 Zr) (hiZ_K.mono_set inter_subset_left)
      have hV_d3 := hsplit_r (phaseEnergyDensity f 0 V)
        ((hiV_K.mono_set inter_subset_left).mono_set hcb_r1_sub)
      have hZ_d3 := hsplit_r (phaseEnergyDensity f 0 Zr)
        ((hiZ_K.mono_set inter_subset_left).mono_set hcb_r1_sub)
      change (∫ x in K_big, phaseEnergyDensity f 0 V x) ≤
        ∫ x in K_big, phaseEnergyDensity f 0 Zr x at hmin_Zr
      have hZ_tot : (∫ x in K_big, phaseEnergyDensity f 0 Zr x) =
          (∫ x in (C₁ ∩ closedBall 0 (r + 1)) \ closedBall 0 r, phaseEnergyDensity f 0 Zr x) +
            (∫ x in (K_big ∩ C₁) \ closedBall 0 (r + 1), phaseEnergyDensity f 0 V x) +
            (∫ x in K_big \ C₁, phaseEnergyDensity f 0 V x) := by
        rw [hZ_d1, hZ_d2, hZ_d3, hz_in, zero_add, heq_outer, heq_off_C₁, add_assoc]
      have hV_tot : (∫ x in K_big, phaseEnergyDensity f 0 V x) =
          I_en (r + 1) +
            (∫ x in (K_big ∩ C₁) \ closedBall 0 (r + 1), phaseEnergyDensity f 0 V x) +
            (∫ x in K_big \ C₁, phaseEnergyDensity f 0 V x) := by
        rw [hV_d1, hV_d2, add_assoc]
      have hI_le_Z : I_en (r + 1) ≤
          ∫ x in (C₁ ∩ closedBall 0 (r + 1)) \ closedBall 0 r, phaseEnergyDensity f 0 Zr x := by
        linarith only [hmin_Zr, hZ_tot, hV_tot]
      have hI_diff : I_en (r + 1) = I_en r +
          ∫ x in (C₁ ∩ closedBall 0 (r + 1)) \ closedBall 0 r, phaseEnergyDensity f 0 V x :=
        hV_d3
      have hsh_V : (∫ x in (C₁ ∩ closedBall 0 (r + 1)) \ closedBall 0 r,
          phaseEnergyDensity f 0 V x) = I_en (r + 1) - I_en r := by
        linarith only [hI_diff]
      rw [hsh_V] at hshell_bound
      exact hI_le_Z.trans hshell_bound
    -- Step 4: Exponential lower bound vs surface-order upper bound
    obtain ⟨x_c, hx_c⟩ := hC₁_ne
    obtain ⟨δ_c, hδ_c, hball_c⟩ := Metric.mem_nhds_iff.mp (hC₁_open.mem_nhds hx_c)
    let r₀ : ℝ := ‖x_c‖ + δ_c + 1
    have hr₀_ge1 : 1 ≤ r₀ := by
      dsimp only [r₀]
      linarith [norm_nonneg x_c]
    have hball_sub_r₀ : ball x_c (δ_c / 2) ⊆ C₁ ∩ closedBall 0 r₀ := by
      intro y hy
      refine ⟨hball_c (ball_subset_ball (by linarith) hy), ?_⟩
      rw [mem_closedBall, dist_zero_right]
      have hd : ‖y - x_c‖ < δ_c / 2 := by simpa only [mem_ball, dist_eq_norm] using hy
      have htri : ‖y‖ ≤ ‖y - x_c‖ + ‖x_c‖ := by
        calc
          ‖y‖ = ‖(y - x_c) + x_c‖ := by congr 1; abel
          _ ≤ ‖y - x_c‖ + ‖x_c‖ := norm_add_le _ _
      dsimp only [r₀]
      linarith
    have hI₀_pos : 0 < I_en r₀ := by
      have hi_r₀ := (h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hV_val 0
        (isCompact_closedBall (0 : Space (m + 1)) r₀)).mono_set (inter_subset_right (s := C₁))
      have hmono_set := setIntegral_mono_set hi_r₀
        (Eventually.of_forall (fun y ↦ phaseEnergyDensity_nonneg_zero
          (hr.normalizedPotential_nonneg h) hV_val y))
        hball_sub_r₀.eventuallyLE
      have hlow_ball : w_min * volume.real (ball x_c (δ_c / 2)) ≤
          ∫ y in ball x_c (δ_c / 2), phaseEnergyDensity f 0 V y := by
        have hi_c : IntegrableOn (fun _ : Space (m + 1) ↦ w_min) (ball x_c (δ_c / 2)) :=
          (continuousOn_const.integrableOn_compact (isCompact_closedBall x_c (δ_c / 2))).mono_set
            ball_subset_closedBall
        have hm := setIntegral_mono_on hi_c (hi_r₀.mono_set hball_sub_r₀) isOpen_ball.measurableSet
          (fun y hy ↦ by
            have hyC : y ∈ C₁ := (hball_sub_r₀ hy).1
            have hpV : 0 < V y := hC₁_sub hyC
            rw [phaseEnergyDensity_eq_kinetic_add_potential (fun z ↦ (hV_val z).1),
              indicator_of_mem (s := {z | 0 < V z}) hpV]
            linarith [sq_nonneg ‖gradient V y‖, hW_lower_C₁ hyC])
        simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hm
      have hvol_pos : 0 < volume.real (ball x_c (δ_c / 2)) :=
        ENNReal.toReal_pos (measure_ball_pos volume x_c (half_pos hδ_c)).ne' measure_ball_ne_top
      exact (mul_pos hw_min_pos hvol_pos).trans_le (hlow_ball.trans hmono_set)
    let q_exp : ℝ := C_shell / (C_shell - 1)
    have hq_gt1 : 1 < q_exp := by
      dsimp only [q_exp]
      exact (one_lt_div (by linarith)).mpr (by linarith)
    have hind_exp (k : ℕ) : q_exp ^ k * I_en r₀ ≤ I_en (r₀ + (k : ℝ)) := by
      induction k with
      | zero => simp
      | succ k ih =>
        have hrk : 1 ≤ r₀ + (k : ℝ) := by
          have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        have hstep := hrec (r₀ + (k : ℝ)) hrk
        have hsub_pos : 0 < C_shell - 1 := by linarith
        have hstep' : q_exp * I_en (r₀ + (k : ℝ)) ≤ I_en (r₀ + (k : ℝ) + 1) := by
          dsimp only [q_exp]
          rw [div_mul_eq_mul_div, div_le_iff₀ hsub_pos]
          linarith
        have hcast : r₀ + ((k + 1 : ℕ) : ℝ) = r₀ + (k : ℝ) + 1 := by push_cast; ring
        rw [hcast, pow_succ', mul_assoc]
        exact (mul_le_mul_of_nonneg_left ih (by linarith)).trans hstep'
    obtain ⟨C_surf, hC_surf, hsurf⟩ :=
      hr.physical_translation_limit_surface_growth h hV hV_val hlim
    -- Bernoulli growth contradiction at `k = N_step * (m + 1)`
    let δ_q : ℝ := q_exp - 1
    have hδ_q : 0 < δ_q := sub_pos.mpr hq_gt1
    obtain ⟨N_step, hN_step⟩ := exists_nat_gt
      (max (r₀ + 1) ((C_surf * ((m : ℝ) + 2) ^ m + 1) / (I_en r₀ * δ_q ^ (m + 1))))
    have hN_gt_r₀ : r₀ + 1 < (N_step : ℝ) := (le_max_left _ _).trans_lt hN_step
    have hN_gt_C : (C_surf * ((m : ℝ) + 2) ^ m + 1) / (I_en r₀ * δ_q ^ (m + 1)) < (N_step : ℝ) :=
      (le_max_right _ _).trans_lt hN_step
    have hN_pos : 0 < (N_step : ℝ) := by linarith
    let k_big : ℕ := N_step * (m + 1)
    have hbern : ((N_step : ℝ) * δ_q) ^ (m + 1) ≤ q_exp ^ k_big := by
      have h1 : 1 + (N_step : ℝ) * δ_q ≤ (1 + δ_q) ^ N_step :=
        one_add_mul_le_pow (by linarith : -2 ≤ δ_q) N_step
      have hq_eq : 1 + δ_q = q_exp := by dsimp only [δ_q]; ring
      rw [hq_eq] at h1
      have h2 : ((N_step : ℝ) * δ_q) ^ (m + 1) ≤ (q_exp ^ N_step) ^ (m + 1) :=
        pow_le_pow_left₀ (by positivity) (by linarith) (m + 1)
      rwa [← pow_mul] at h2
    have hlow_k : I_en r₀ * δ_q ^ (m + 1) * (N_step : ℝ) * (N_step : ℝ) ^ m ≤
        I_en (r₀ + (k_big : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_right hbern hI₀_pos.le
      have hrew : ((N_step : ℝ) * δ_q) ^ (m + 1) * I_en r₀ =
          I_en r₀ * δ_q ^ (m + 1) * (N_step : ℝ) * (N_step : ℝ) ^ m := by
        rw [mul_pow, pow_succ]
        ring
      rw [hrew] at h1
      exact h1.trans (hind_exp k_big)
    have hup_k : I_en (r₀ + (k_big : ℝ)) ≤
        C_surf * ((m : ℝ) + 2) ^ m * (N_step : ℝ) ^ m := by
      have hrk : 1 ≤ r₀ + (k_big : ℝ) := by
        have hk0 : 0 ≤ (k_big : ℝ) := Nat.cast_nonneg k_big
        linarith
      have hle_ball : I_en (r₀ + (k_big : ℝ)) ≤
          ∫ x in closedBall 0 (r₀ + (k_big : ℝ)), phaseEnergyDensity f 0 V x :=
        setIntegral_mono_set
          (h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hV_val 0
            (isCompact_closedBall _ _))
          (Eventually.of_forall (fun y ↦ phaseEnergyDensity_nonneg_zero
            (hr.normalizedPotential_nonneg h) hV_val y))
          inter_subset_right.eventuallyLE
      have hrad_le : r₀ + (k_big : ℝ) ≤ ((m : ℝ) + 2) * (N_step : ℝ) := by
        have hk_eq : (k_big : ℝ) = (N_step : ℝ) * ((m : ℝ) + 1) := by
          dsimp only [k_big]; push_cast; ring
        rw [hk_eq]
        linarith only [hN_gt_r₀, hN_pos]
      have hpow_le : (r₀ + (k_big : ℝ)) ^ m ≤ (((m : ℝ) + 2) * (N_step : ℝ)) ^ m :=
        pow_le_pow_left₀ (by linarith only [hrk]) hrad_le m
      rw [mul_pow] at hpow_le
      calc
        I_en (r₀ + (k_big : ℝ)) ≤ C_surf * (r₀ + (k_big : ℝ)) ^ m :=
          hle_ball.trans (hsurf _ hrk)
        _ ≤ C_surf * (((m : ℝ) + 2) ^ m * (N_step : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_left hpow_le hC_surf.le
        _ = C_surf * ((m : ℝ) + 2) ^ m * (N_step : ℝ) ^ m := by ring
    have hcoeff_gt : C_surf * ((m : ℝ) + 2) ^ m + 1 <
        I_en r₀ * δ_q ^ (m + 1) * (N_step : ℝ) :=
      ((div_lt_iff₀ (mul_pos hI₀_pos (pow_pos hδ_q (m + 1)))).mp hN_gt_C).trans_eq (mul_comm _ _)
    have hNm_pos : 0 < (N_step : ℝ) ^ m := pow_pos hN_pos m
    have hmul_strict := mul_lt_mul_of_pos_right hcoeff_gt hNm_pos
    rw [add_mul, one_mul] at hmul_strict
    linarith only [hmul_strict, hlow_k, hup_k, hNm_pos]
  -- Step 5: Conclude `IsPreconnected Ω_V` from `hV_union_pre` and `hexclude_piece`
  intro U₁ U₂ hU₁ hU₂ hcov hne₁ hne₂
  by_contra hdisj
  rw [not_nonempty_iff_eq_empty] at hdisj
  let Ω₁ := Ω_V ∩ U₁
  let Ω₂ := Ω_V ∩ U₂
  have hΩ₁_open : IsOpen Ω₁ := hΩ_open.inter hU₁
  have hΩ₂_open : IsOpen Ω₂ := hΩ_open.inter hU₂
  have hΩ₁_comp : Ω_V \ Ω₁ = Ω₂ := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, Ω₁, Ω₂]
    constructor
    · rintro ⟨hx, hnot⟩
      have hx12 := hcov hx
      rcases hx12 with hx1 | hx2
      · exact False.elim (hnot ⟨hx, hx1⟩)
      · exact ⟨hx, hx2⟩
    · rintro ⟨hx, hx2⟩
      refine ⟨hx, fun ⟨_, hx1⟩ ↦ ?_⟩
      have hm : x ∈ Ω_V ∩ (U₁ ∩ U₂) := ⟨hx, hx1, hx2⟩
      rw [hdisj] at hm
      exact notMem_empty x hm
  have hΩ₂_comp : Ω_V \ Ω₂ = Ω₁ := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, Ω₁, Ω₂]
    constructor
    · rintro ⟨hx, hnot⟩
      rcases hcov hx with hx1 | hx2
      · exact ⟨hx, hx1⟩
      · exact False.elim (hnot ⟨hx, hx2⟩)
    · rintro ⟨hx, hx1⟩
      refine ⟨hx, fun ⟨_, hx2⟩ ↦ ?_⟩
      have hm : x ∈ Ω_V ∩ (U₁ ∩ U₂) := ⟨hx, hx1, hx2⟩
      rw [hdisj] at hm
      exact notMem_empty x hm
  -- `V_union` is preconnected and contained in `U₁ ∪ U₂` with `V_union ∩ (U₁ ∩ U₂) = ∅`
  by_cases hV1 : (V_union ∩ U₁).Nonempty
  · by_cases hV2 : (V_union ∩ U₂).Nonempty
    · obtain ⟨z, hzV, hzab⟩ := hV_union_pre U₁ U₂ hU₁ hU₂ (hV_union_sub.trans hcov) hV1 hV2
      have hm : z ∈ Ω_V ∩ (U₁ ∩ U₂) := ⟨hV_union_sub hzV, hzab⟩
      rw [hdisj] at hm
      exact notMem_empty z hm
    · rw [not_nonempty_iff_eq_empty] at hV2
      have hdisj2 : Disjoint Ω₂ V_union := by
        rw [disjoint_iff_inter_eq_empty]
        ext x
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, Ω₂]
        rintro ⟨⟨_, hxU₂⟩, hxV⟩
        have hm : x ∈ V_union ∩ U₂ := ⟨hxV, hxU₂⟩
        rw [hV2] at hm
        exact notMem_empty x hm
      exact hexclude_piece hΩ₂_open inter_subset_left (by rwa [hΩ₂_comp]) hne₂ hdisj2
  · rw [not_nonempty_iff_eq_empty] at hV1
    have hdisj1 : Disjoint Ω₁ V_union := by
      rw [disjoint_iff_inter_eq_empty]
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, Ω₁]
      rintro ⟨⟨_, hxU₁⟩, hxV⟩
      have hm : x ∈ V_union ∩ U₁ := ⟨hxV, hxU₁⟩
      rw [hV1] at hm
      exact notMem_empty x hm
    exact hexclude_piece hΩ₁_open inter_subset_left (by rwa [hΩ₁_comp]) hne₁ hdisj1

/-- **Half-ball positivity propagation for nonnegative differences of positive physical limits**:
If `V ≤ V_tilde` are physical translation limits and `closedBall c R ⊆ {y | 0 < V y}` (`0 < R`),
then `V c < V_tilde c` implies `V x < V_tilde x` for every `x ∈ ball c R`. -/
theorem RigidityHypotheses.pos_on_ball_of_ordered_physical_limits
    {m : ℕ} {g : Space m → ℝ} {u V V_tilde : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ R : ℝ}
    {c : Space (m + 1)} {p_seq q_seq : ℕ → Space (m + 1)}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hR : 0 < R) (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hVt : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V_tilde)
    (hV_val : ∀ x, V x ∈ Icc 0 1) (hVt_val : ∀ x, V_tilde x ∈ Icc 0 1)
    (hV_lim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V atTop K)
    (hVt_lim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (q_seq j + x)) V_tilde atTop K)
    (horder : ∀ x, V x ≤ V_tilde x)
    (hball : closedBall c R ⊆ {y | 0 < V y}) (hc : V c < V_tilde c) :
    ∀ x ∈ ball c R, V x < V_tilde x := by
  obtain ⟨Lf, hLf⟩ := (h.reaction_contDiffOn.mono Icc_subset_Ici_self).exists_lipschitzOnWith
    one_ne_zero (convex_Icc 0 1) isCompact_Icc
  let M : ℝ := (Lf : ℝ) + 1
  have hM_pos : 0 < M := by dsimp only [M]; positivity
  let ε : ℝ := (V_tilde c - V c) / 2
  have hε_pos : 0 < ε := half_pos (sub_pos.mpr hc)
  have hev_c : ∀ᶠ y in 𝓝 c, ε < V_tilde y - V y :=
    ((hVt.continuous.sub hV.continuous).continuousAt (x := c)).eventually
      (Ioi_mem_nhds (half_lt_self (sub_pos.mpr hc)))
  obtain ⟨s₀, hs₀, hsv⟩ := Metric.eventually_nhds_iff.mp hev_c
  let r₀ : ℝ := min (s₀ / 2) (R / 2)
  have hr₀_pos : 0 < r₀ := lt_min (half_pos hs₀) (half_pos hR)
  have hinner (y : Space (m + 1)) (hy : y ∈ closedBall c r₀) : ε ≤ V_tilde y - V y :=
    (hsv (hy.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hs₀)))).le
  obtain ⟨α, hα, hparam⟩ := exists_annularBarrier_parameter (E := Space (m + 1)) hr₀_pos hM_pos.le
  intro x₀ hx₀
  have hbar_pos : 0 < ε * annularBarrier c α R x₀ :=
    mul_pos hε_pos (annularBarrier_pos hα hR.le (by simpa only [mem_ball, dist_eq_norm] using hx₀))
  suffices hle : ε * annularBarrier c α R x₀ ≤ V_tilde x₀ - V x₀ by linarith
  by_contra hlt_x₀
  push Not at hlt_x₀
  let δ : ℝ := (ε * annularBarrier c α R x₀ - (V_tilde x₀ - V x₀)) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  let β : Space (m + 1) → ℝ := fun x ↦ ε * annularBarrier c α R x
  let w : Space (m + 1) → ℝ := fun x ↦ V_tilde x - V x - β x + δ
  let ψ : Space (m + 1) → ℝ := fun x ↦ max (-w x) 0
  have hβ_cd : ContDiff ℝ (⊤ : ℕ∞) β := contDiff_const.mul (contDiff_annularBarrier c α R)
  have hβ_cd2 : ContDiff ℝ 2 β := hβ_cd.of_le (by simp)
  have hw_lip : LocallyLipschitz w :=
    ((hVt.locallyLipschitz.sub hV.locallyLipschitz).sub
      (hβ_cd.of_le (by simp)).locallyLipschitz).add
        ((contDiff_const (c := δ) : ContDiff ℝ 1 (fun _ : Space (m + 1) ↦ δ)).locallyLipschitz)
  have hψ_lip : LocallyLipschitz ψ := locallyLipschitz_posPart_real hw_lip.neg
  let A_ann : Set (Space (m + 1)) := {x | r₀ < ‖x - c‖ ∧ ‖x - c‖ < R}
  have hψ_supp : tsupport ψ ⊆ A_ann := by
    have hsub_le : tsupport ψ ⊆ {x | w x ≤ 0} := by
      apply closure_minimal _ (isClosed_le hw_lip.continuous continuous_const)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hpos_w
      exact hx (max_eq_right (neg_nonpos.mpr (not_le.mp hpos_w).le))
    refine hsub_le.trans (fun x hx ↦ ⟨?_, ?_⟩)
    · by_contra hle_in
      push Not at hle_in
      have hx_cb : x ∈ closedBall c r₀ := by
        simpa only [mem_closedBall, dist_eq_norm] using hle_in
      have h1 : ε ≤ V_tilde x - V x := hinner x hx_cb
      have h2 : β x < ε := mul_lt_of_lt_one_right hε_pos (annularBarrier_lt_one c x hα.le R)
      have hwx : V_tilde x - V x - β x + δ ≤ 0 := hx
      linarith
    · by_contra hge_out
      push Not at hge_out
      have hb_np := annularBarrier_nonpos hα.le hR.le hge_out
      have h1 : 0 ≤ V_tilde x - V x := sub_nonneg.mpr (horder x)
      have h2 : β x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε_pos.le hb_np
      have hwx : V_tilde x - V x - β x + δ ≤ 0 := hx
      linarith
  have hA_sub_ball : A_ann ⊆ ball c R := fun x hx ↦ by
    simpa only [mem_ball, dist_eq_norm] using hx.2
  have hcψ : HasCompactSupport ψ :=
    (isCompact_closedBall c R).of_isClosed_subset (isClosed_tsupport _)
      ((hψ_supp.trans hA_sub_ball).trans ball_subset_closedBall)
  have hsub_pos_V : tsupport ψ ⊆ {y | 0 < V y} :=
    ((hψ_supp.trans hA_sub_ball).trans ball_subset_closedBall).trans hball
  have hsub_pos_Vt : tsupport ψ ⊆ {y | 0 < V_tilde y} :=
    hsub_pos_V.trans (fun y hy ↦ lt_of_lt_of_le hy (horder y))
  have htest_V := hr.physical_translation_limit_positive_lipschitz_test h hV hV_val hV_lim
    hψ_lip hcψ hsub_pos_V
  have htest_Vt := hr.physical_translation_limit_positive_lipschitz_test h hVt hVt_val hVt_lim
    hψ_lip hcψ hsub_pos_Vt
  -- Smooth cutoff IBP for `β`
  obtain ⟨Bψ, hBψ⟩ := hcψ.exists_bound_of_continuous hψ_lip.continuous
  have hψ_val (x : Space (m + 1)) : ψ x ∈ Icc 0 Bψ :=
    ⟨le_max_right _ _, (le_abs_self _).trans (hBψ x)⟩
  let θ_b : ContDiffBump c :=
    { rIn := R + 1
      rOut := R + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let X_β : Space (m + 1) → Space (m + 1) :=
    fun x ↦ (θ_b : Space (m + 1) → ℝ) x • gradient β x
  have hX_β : ContDiff ℝ 1 X_β :=
    θ_b.contDiff.smul ((toDual ℝ (Space (m + 1))).symm.contDiff.comp
      (hβ_cd2.fderiv_right (by norm_num)))
  have hcX_β : HasCompactSupport X_β := θ_b.hasCompactSupport.smul_right
  let b_std := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hibp_β := integral_fieldDivergence_mul_eq_neg_inner_gradient_of_locallyLipschitz
    b_std hψ_lip hψ_val hX_β hcX_β
  have hβ_ibp : (∫ x, inner ℝ (gradient β x) (gradient ψ x)) =
      -∫ x, (Δ β) x * ψ x := by
    have hL : (∫ x, inner ℝ (gradient ψ x) (X_β x)) =
        ∫ x, inner ℝ (gradient β x) (gradient ψ x) := by
      apply integral_congr_ae
      refine Eventually.of_forall (fun x ↦ ?_)
      dsimp only [X_β]
      by_cases hx : x ∈ tsupport ψ
      · have hxb : x ∈ closedBall c (R + 1) := by
          have h1 : dist x c < R := hA_sub_ball (hψ_supp hx)
          rw [mem_closedBall]; linarith
        rw [θ_b.one_of_mem_closedBall hxb, one_smul, real_inner_comm]
      · simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
    have hR_eq : (∫ x, ψ x * fieldDivergence b_std X_β x) = ∫ x, (Δ β) x * ψ x := by
      apply integral_congr_ae
      refine Eventually.of_forall (fun x ↦ ?_)
      dsimp only
      by_cases hx : x ∈ tsupport ψ
      · have hxb : x ∈ ball c (R + 1) := by
          have h1 : dist x c < R := hA_sub_ball (hψ_supp hx)
          rw [mem_ball]; linarith
        have hev : X_β =ᶠ[𝓝 x] gradient β := by
          filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
          dsimp only [X_β]
          rw [θ_b.one_of_mem_closedBall (ball_subset_closedBall hy), one_smul]
        have hdiv_eq : fieldDivergence b_std X_β x = (Δ β) x := by
          have hgβ_diff : DifferentiableAt ℝ (gradient β) x := by
            unfold gradient
            exact ((toDual ℝ (Space (m + 1))).symm.contDiff.comp
              (hβ_cd2.fderiv_right (by norm_num))).differentiable one_ne_zero x
          have hh := laplacian_eq_sum_gradient_derivative_of_differentiable hgβ_diff b_std
          rw [hh]
          unfold fieldDivergence
          refine Finset.sum_congr rfl (fun i _ ↦ ?_)
          rw [hev.fderiv_eq]
          exact real_inner_comm _ _
        rw [hdiv_eq, mul_comm]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
    rw [← hL, ← hR_eq, hibp_β, neg_neg]
  have hβ_sub_int : 0 ≤ -(∫ x, inner ℝ (gradient β x) (gradient ψ x)) -
      ∫ x, M * β x * ψ x := by
    rw [hβ_ibp, neg_neg]
    have hi1 : Integrable (fun x ↦ (Δ β) x * ψ x) :=
      ((continuous_laplacian_of_contDiff hβ_cd2).mul
        hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
    have hi2 : Integrable (fun x ↦ M * β x * ψ x) :=
      ((continuous_const.mul hβ_cd.continuous).mul
        hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
    rw [← integral_sub hi1 hi2]
    apply integral_nonneg
    intro x
    dsimp only [Pi.sub_apply]
    by_cases hx : x ∈ tsupport ψ
    · have hxA := hψ_supp hx
      have hlap_β : (Δ β) x = ε * (Δ (annularBarrier c α R)) x := by
        change (Δ (ε • annularBarrier c α R)) x = _
        exact laplacian_smul ε (contDiff_annularBarrier c α R (n := 2)).contDiffAt
      have hsub_bar := annularBarrier_subsolution (R := R) hM_pos.le hr₀_pos.le hxA.1.le hparam
      have hmul := mul_nonneg hε_pos.le hsub_bar
      have hrew : (Δ β) x * ψ x - M * β x * ψ x =
          (ε * ((Δ (annularBarrier c α R)) x - M * annularBarrier c α R x)) * ψ x := by
        dsimp only [β]; rw [hlap_β]; ring
      rw [hrew]
      exact mul_nonneg hmul (le_max_right _ _)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hfV_cont : Continuous (fun x ↦ f (V x)) :=
    h.reaction_contDiffOn.continuousOn.comp_continuous hV.continuous (fun x ↦ (hV_val x).1)
  have hfVt_cont : Continuous (fun x ↦ f (V_tilde x)) :=
    h.reaction_contDiffOn.continuousOn.comp_continuous hVt.continuous (fun x ↦ (hVt_val x).1)
  have hV_gb (x : Space (m + 1)) : ‖gradient V x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]; exact norm_fderiv_le_of_lipschitz ℝ hV
  have hVt_gb (x : Space (m + 1)) : ‖gradient V_tilde x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]; exact norm_fderiv_le_of_lipschitz ℝ hVt
  have hig_V : Integrable (fun x ↦ inner ℝ (gradient V x) (gradient ψ x)) := by
    simpa using integrable_weak_residual_of_locallyLipschitz_test
      (measurable_gradient V) (measurable_const (a := (0 : ℝ))) hV_gb (fun _ ↦ le_rfl) hψ_lip hcψ
  have hig_Vt : Integrable (fun x ↦ inner ℝ (gradient V_tilde x) (gradient ψ x)) := by
    simpa using integrable_weak_residual_of_locallyLipschitz_test
      (measurable_gradient V_tilde) (measurable_const (a := (0 : ℝ))) hVt_gb
      (fun _ ↦ le_rfl) hψ_lip hcψ
  have hig_β : Integrable (fun x ↦ inner ℝ (gradient β x) (gradient ψ x)) := by
    obtain ⟨Cβ, hCβ⟩ := gradient_bound_of_locallyLipschitz
      (hβ_cd.of_le (by simp)).locallyLipschitz hcψ
    obtain ⟨Cg, hCg⟩ := gradient_bound_of_locallyLipschitz hψ_lip hcψ
    have hig_on : IntegrableOn (fun x ↦ inner ℝ (gradient β x) (gradient ψ x)) (tsupport ψ) := by
      apply (continuousOn_const.integrableOn_compact hcψ
        (f := fun _ : Space (m + 1) ↦ (Cβ : ℝ) * (Cg : ℝ))).mono'
        ((measurable_gradient β).inner (𝕜 := ℝ) (measurable_gradient ψ)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem (isClosed_tsupport ψ).measurableSet] with x hx
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (hCβ x hx) (hCg x hx) (norm_nonneg _) Cβ.coe_nonneg)
    exact hig_on.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      simp [gradient, fderiv_of_notMem_tsupport ℝ hx])
  have his_V : Integrable (fun x ↦ f (V x) * ψ x) :=
    (hfV_cont.mul hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have his_Vt : Integrable (fun x ↦ f (V_tilde x) * ψ x) :=
    (hfVt_cont.mul hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have hi_Mdiff : Integrable (fun x ↦ M * (V_tilde x - V x) * ψ x) :=
    ((continuous_const.mul (hVt.continuous.sub hV.continuous)).mul
      hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have hi_Mβ : Integrable (fun x ↦ M * β x * ψ x) :=
    ((continuous_const.mul hβ_cd.continuous).mul
      hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have hi_Mδ : Integrable (fun x ↦ M * δ * ψ x) :=
    (continuous_const.mul hψ_lip.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  rw [integral_sub hig_V his_V] at htest_V
  rw [integral_sub hig_Vt his_Vt] at htest_Vt
  have hreac_nn : 0 ≤ (∫ x, f (V_tilde x) * ψ x) - (∫ x, f (V x) * ψ x) +
      ∫ x, M * (V_tilde x - V x) * ψ x := by
    have hsub1 := integral_sub his_Vt his_V
    have hadd1 := integral_add (his_Vt.sub his_V) hi_Mdiff
    dsimp only [Pi.sub_apply] at hadd1
    rw [← hsub1, ← hadd1]
    apply integral_nonneg
    intro x
    dsimp only [Pi.zero_apply]
    have hd_f := hLf.dist_le_mul (V_tilde x) (hVt_val x) (V x) (hV_val x)
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (horder x))] at hd_f
    have h1 : -(Lf : ℝ) * (V_tilde x - V x) ≤ f (V_tilde x) - f (V x) := by
      linarith [neg_abs_le (f (V_tilde x) - f (V x))]
    have h2 : 0 ≤ (f (V_tilde x) - f (V x) + M * (V_tilde x - V x)) * ψ x := by
      apply mul_nonneg _ (le_max_right _ _)
      dsimp only [M]
      nlinarith [horder x]
    linarith
  have hδ_nn : 0 ≤ ∫ x, M * δ * ψ x :=
    integral_nonneg (fun _ ↦ mul_nonneg (mul_nonneg hM_pos.le hδ.le) (le_max_right _ _))
  have hgrad_split : (∫ x, inner ℝ (gradient V_tilde x) (gradient ψ x)) -
      (∫ x, inner ℝ (gradient V x) (gradient ψ x)) -
      (∫ x, inner ℝ (gradient β x) (gradient ψ x)) ≤ 0 := by
    have hsub1 := integral_sub hig_Vt hig_V
    have hsub2 := integral_sub (hig_Vt.sub hig_V) hig_β
    dsimp only [Pi.sub_apply] at hsub2
    rw [← hsub1, ← hsub2]
    apply integral_nonpos_of_ae
    filter_upwards [ae_differentiableAt_of_locallyLipschitz hV.locallyLipschitz,
      ae_differentiableAt_of_locallyLipschitz hVt.locallyLipschitz,
      ae_differentiableAt_of_locallyLipschitz hψ_lip] with x hdV hdVt _
    dsimp only [Pi.zero_apply]
    have hdβ : DifferentiableAt ℝ β x :=
      (hβ_cd2.of_le (by norm_num)).differentiable one_ne_zero x
    have hgw : gradient w x = gradient V_tilde x - gradient V x - gradient β x := by
      have hfw : HasFDerivAt w (fderiv ℝ V_tilde x - fderiv ℝ V x - fderiv ℝ β x) x :=
        ((hdVt.hasFDerivAt.sub hdV.hasFDerivAt).sub hdβ.hasFDerivAt).add_const δ
      simp only [gradient, hfw.fderiv, map_sub]
    have hlin : inner ℝ (gradient V_tilde x) (gradient ψ x) -
        inner ℝ (gradient V x) (gradient ψ x) -
        inner ℝ (gradient β x) (gradient ψ x) =
        inner ℝ (gradient w x) (gradient ψ x) := by
      rw [hgw, inner_sub_left, inner_sub_left]
    rw [hlin]
    by_cases hneg : w x < 0
    · have hev : ψ =ᶠ[𝓝 x] fun y ↦ -w y := by
        filter_upwards [(isOpen_lt hw_lip.continuous continuous_const).mem_nhds hneg] with y hy
        exact max_eq_left (neg_nonneg.mpr hy.le)
      have hgψ : gradient ψ x = -gradient w x := by rw [hev.gradient_eq]; simp [gradient]
      rw [hgψ, inner_neg_right, real_inner_self_eq_norm_sq]
      exact neg_nonpos.mpr (sq_nonneg _)
    · push Not at hneg
      have hψ0 : ψ x = 0 := max_eq_right (neg_nonpos.mpr hneg)
      have hmin_ψ : IsLocalMin ψ x := by
        filter_upwards with y; rw [hψ0]; exact le_max_right _ _
      have hgψ : gradient ψ x = 0 := by simp [gradient, hmin_ψ.fderiv_eq_zero]
      rw [hgψ, inner_zero_right]
  have hmass_eq : (∫ x, M * (V_tilde x - V x) * ψ x) - (∫ x, M * β x * ψ x) +
      (∫ x, M * δ * ψ x) = -(M * ∫ x, ψ x ^ 2) := by
    have hsub1 := integral_sub hi_Mdiff hi_Mβ
    have hadd1 := integral_add (hi_Mdiff.sub hi_Mβ) hi_Mδ
    dsimp only [Pi.sub_apply] at hadd1
    rw [← hsub1, ← hadd1, ← integral_const_mul, ← integral_neg]
    apply integral_congr_ae
    refine Eventually.of_forall (fun x ↦ ?_)
    dsimp only [Pi.neg_apply]
    have h1 : M * (V_tilde x - V x) * ψ x - M * β x * ψ x + M * δ * ψ x =
        M * w x * ψ x := by dsimp only [w]; ring
    rw [h1]
    by_cases hneg : w x < 0
    · dsimp only [ψ]; rw [max_eq_left (neg_nonneg.mpr hneg.le)]; ring
    · push Not at hneg; dsimp only [ψ]; rw [max_eq_right (neg_nonpos.mpr hneg)]; ring
  have hψ_sq_le : M * (∫ x, ψ x ^ 2) ≤ 0 := by
    linarith [htest_V, htest_Vt, hβ_sub_int, hreac_nn, hδ_nn, hgrad_split, hmass_eq]
  have hψ_x₀_pos : 0 < ψ x₀ := by
    dsimp only [ψ, w, β, δ]; apply lt_max_of_lt_left; linarith
  have hψ_sq_cont : Continuous (fun x ↦ ψ x ^ 2) := hψ_lip.continuous.pow 2
  have hcψ_sq : HasCompactSupport (fun x ↦ ψ x ^ 2) :=
    hcψ.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset (g := fun t : ℝ ↦ t ^ 2) (by simp) ψ)
  have hψ_sq_pos : 0 < ∫ x, ψ x ^ 2 :=
    integral_pos_of_integrable_nonneg_nonzero hψ_sq_cont
      (hψ_sq_cont.integrable_of_hasCompactSupport hcψ_sq)
      (fun _ ↦ sq_nonneg _) (pow_ne_zero 2 hψ_x₀_pos.ne')
  exact (not_lt_of_ge hψ_sq_le) (mul_pos hM_pos hψ_sq_pos)

/-- **Strict interior translation order and zero critical contact (DS9.2–DS9.3)**:
If `V` is a physical translation limit with `0 ∈ closure {x | 0 < V x}`, `V a₀ = V 0`,
`V 0 < 1`, `a₀ ∈ translationOrderSet V`, and `0 < inner ℝ e a₀` under
`HasUniformBoundaryCoarseCone g e` (`‖e‖ = 1`), then:
1. `∀ y, 0 < V y → V y < V (y + a₀)`, and
2. `V 0 = 0 ∧ V a₀ = 0`. -/
theorem RigidityHypotheses.critical_contact_strict_and_zero
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    {e a₀ : Space (m + 1)} {p : ℕ → Space (m + 1)}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (he : ‖e‖ = 1) (hcone : HasUniformBoundaryCoarseCone g e)
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hV_val : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hcl0 : (0 : Space (m + 1)) ∈ closure {x | 0 < V x})
    (ha₀_ord : a₀ ∈ translationOrderSet V) (ha₀_in : 0 < inner ℝ e a₀)
    (heq_contact : V a₀ = V 0) (hV0_lt : V 0 < 1) :
    (∀ y, 0 < V y → V y < V (y + a₀)) ∧ V 0 = 0 ∧ V a₀ = 0 := by
  let Ω_V : Set (Space (m + 1)) := {y | 0 < V y}
  have hΩ_open : IsOpen Ω_V := isOpen_lt continuous_const hV.continuous
  have hΩ_conn : IsPreconnected Ω_V :=
    hr.isPreconnected_positive_phase_of_coarse_cone h he hcone hV hV_val hlim hcl0 hV0_lt
  obtain ⟨hV_lt_one, hΩ_ne_univ⟩ := hr.physical_translation_limit_lt_one_and_not_univ h hlim hV0_lt
  have hΩ_ne : Ω_V.Nonempty := closure_nonempty_iff.mp ⟨0, hcl0⟩
  obtain ⟨q₀, hq₀_front⟩ := nonempty_frontier_iff.mpr ⟨hΩ_ne, hΩ_ne_univ⟩
  -- Shifted limit `V_tilde y = V (y + a₀)`
  let V_tilde : Space (m + 1) → ℝ := fun y ↦ V (y + a₀)
  let q_seq : ℕ → Space (m + 1) := fun j ↦ p j + a₀
  have hVt : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V_tilde :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      simpa only [V_tilde, dist_add_right] using hV.dist_le_mul (x + a₀) (y + a₀)
  have hVt_val (y : Space (m + 1)) : V_tilde y ∈ Icc 0 1 := hV_val (y + a₀)
  have hVt_lim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j y ↦ zeroExtension g u (q_seq j + y)) V_tilde atTop K := by
    intro K hK
    have hKa : IsCompact ((fun y ↦ y + a₀) '' K) :=
      hK.image (by fun_prop)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hlim _ hKa) ε hε] with j hj y hy
    have hd := hj (y + a₀) ⟨y, hy, rfl⟩
    have heq_add : p j + (y + a₀) = q_seq j + y := by dsimp only [q_seq]; abel
    rwa [heq_add] at hd
  -- Show `∃ y₀ ∈ Ω_V, V y₀ < V (y₀ + a₀)` by iterating `+ a₀` into a large positive-cone ball
  have hex_strict : ∃ y₀ ∈ Ω_V, 0 < V_tilde y₀ - V y₀ := by
    by_contra hall_eq
    push Not at hall_eq
    obtain ⟨y₁, hy₁⟩ := hΩ_ne
    have hiter (k : ℕ) : y₁ + (k : ℝ) • a₀ ∈ Ω_V ∧ V (y₁ + (k : ℝ) • a₀) = V y₁ := by
      induction k with
      | zero => simp [hy₁]
      | succ k ih =>
        have hstep_le : V_tilde (y₁ + (k : ℝ) • a₀) - V (y₁ + (k : ℝ) • a₀) ≤ 0 :=
          hall_eq _ ih.1
        have hstep_ge : V (y₁ + (k : ℝ) • a₀) ≤ V_tilde (y₁ + (k : ℝ) • a₀) :=
          ha₀_ord (y₁ + (k : ℝ) • a₀)
        have hstep_eq : V ((y₁ + (k : ℝ) • a₀) + a₀) = V y₁ := by
          dsimp only [V_tilde] at hstep_le hstep_ge
          linarith [ih.2]
        have hvec : y₁ + ((k + 1 : ℕ) : ℝ) • a₀ = (y₁ + (k : ℝ) • a₀) + a₀ := by
          push_cast; module
        rw [hvec]
        exact ⟨by change 0 < V _; rw [hstep_eq]; exact hy₁, hstep_eq⟩
    -- Choose `a_mid ∈ (V y₁, 1)` and large-ball radius `R_mid`
    let a_mid : ℝ := (V y₁ + 1) / 2
    have ha_mid : a_mid ∈ Ioo (0 : ℝ) 1 :=
      ⟨by have : 0 < V y₁ := hy₁; dsimp only [a_mid]; linarith,
       by dsimp only [a_mid]; linarith [hV_lt_one y₁]⟩
    have hfa_pos : 0 < f a_mid := hr.reaction_pos a_mid ha_mid
    let N : ℝ := (Module.finrank ℝ (Space (m + 1)) : ℝ) + 2
    have hN_pos : 0 < N := by dsimp only [N]; positivity
    let q_rate : ℝ := f a_mid / a_mid
    have hq_pos : 0 < q_rate := div_pos hfa_pos ha_mid.1
    let R_mid : ℝ := N / Real.sqrt q_rate + 1
    have hR_mid : 0 < R_mid := by dsimp only [R_mid]; positivity
    have hgap_mid : N ^ 2 / R_mid ^ 2 < f a_mid / a_mid := by
      have hgt : N / Real.sqrt q_rate < R_mid := by dsimp only [R_mid]; linarith
      have h1 : N < R_mid * Real.sqrt q_rate := (div_lt_iff₀ (Real.sqrt_pos.mpr hq_pos)).mp hgt
      have h2 : N ^ 2 < R_mid ^ 2 * (Real.sqrt q_rate) ^ 2 := by
        nlinarith [Real.sqrt_pos.mpr hq_pos]
      rw [Real.sq_sqrt hq_pos.le] at h2
      exact (div_lt_iff₀ (sq_pos_of_pos hR_mid)).mpr (by simpa only [q_rate, mul_comm] using h2)
    have ha₀_norm_pos : 0 < ‖a₀‖ := by
      have hle : inner ℝ e a₀ ≤ ‖a₀‖ := by
        simpa only [he, one_mul] using real_inner_le_norm e a₀
      exact ha₀_in.trans_le hle
    let α_dir : ℝ := inner ℝ e a₀ / ‖a₀‖
    have hα_pos : 0 < α_dir := div_pos ha₀_in ha₀_norm_pos
    let B_shift : ℝ := ‖y₁ - q₀‖ + R_mid + 1
    have hα_le1 : α_dir ≤ 1 := (div_le_one ha₀_norm_pos).mpr (by
      simpa only [he, one_mul] using real_inner_le_norm e a₀)
    let η_a : ℝ := α_dir / 2
    have hη_a : η_a ∈ Ioo (0 : ℝ) 1 := ⟨half_pos hα_pos, by dsimp only [η_a]; linarith⟩
    obtain ⟨R₁, hR₁, hR₁_cone⟩ := hcone η_a hη_a
    obtain ⟨k, hk⟩ := exists_nat_gt ((R₁ + B_shift + 1) * (4 / inner ℝ e a₀))
    have hk_in : 4 * (R₁ + B_shift + 1) < (k : ℝ) * inner ℝ e a₀ := by
      have hm := mul_lt_mul_of_pos_right hk ha₀_in
      have hsimp : (R₁ + B_shift + 1) * (4 / inner ℝ e a₀) * inner ℝ e a₀ =
          4 * (R₁ + B_shift + 1) := by field_simp [ha₀_in.ne']
      rwa [hsimp] at hm
    have hk_pos : 0 < (k : ℝ) := by
      by_contra hnp
      have hk0 : (k : ℝ) ≤ 0 := not_lt.mp hnp
      have h1 : (k : ℝ) * inner ℝ e a₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk0 ha₀_in.le
      have h2 : 0 < 4 * (R₁ + B_shift + 1) := by dsimp only [B_shift]; positivity
      linarith
    have hev_front := hr.eventually_exists_frontier_near_limit_frontier h hV hV_val hlim
      hq₀_front zero_lt_one
    have hpt_k : Tendsto (fun j ↦ zeroExtension g u (p j + (y₁ + (k : ℝ) • a₀))) atTop
        (𝓝 (V (y₁ + (k : ℝ) • a₀))) :=
      (hlim {y₁ + (k : ℝ) • a₀} isCompact_singleton).tendsto_at (mem_singleton _)
    have ha_le_Vk : a_mid ≤ V (y₁ + (k : ℝ) • a₀) := by
      apply ge_of_tendsto hpt_k
      filter_upwards [hev_front] with j ⟨yj, hyj_ball, hyj_front⟩
      have hqy : ‖q₀ - yj‖ < 1 := by
        simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hyj_ball
      have hball_ep : closedBall (p j + (y₁ + (k : ℝ) • a₀)) R_mid ⊆ epigraph g := by
        intro z hz
        let v_s : Space (m + 1) := (z - (p j + (y₁ + (k : ℝ) • a₀))) + (y₁ - q₀) + (q₀ - yj)
        let w' : Space (m + 1) := (k : ℝ) • a₀ + v_s
        have hvs_le : ‖v_s‖ ≤ B_shift := by
          have hz_le : ‖z - (p j + (y₁ + (k : ℝ) • a₀))‖ ≤ R_mid := by
            simpa only [mem_closedBall, dist_eq_norm] using hz
          have htri := (norm_add_le ((z - (p j + (y₁ + (k : ℝ) • a₀))) + (y₁ - q₀)) (q₀ - yj)).trans
            (add_le_add (norm_add_le _ _) le_rfl)
          dsimp only [B_shift]
          linarith
        have hka_norm : ‖(k : ℝ) • a₀‖ = (k : ℝ) * ‖a₀‖ := by
          rw [norm_smul, Real.norm_of_nonneg hk_pos.le]
        have hka_ge : (k : ℝ) * inner ℝ e a₀ ≤ (k : ℝ) * ‖a₀‖ := by
          have hle : inner ℝ e a₀ ≤ ‖a₀‖ := by
            simpa only [he, one_mul] using real_inner_le_norm e a₀
          exact mul_le_mul_of_nonneg_left hle hk_pos.le
        have hw'_ge : R₁ ≤ ‖w'‖ := by
          have htri : ‖(k : ℝ) • a₀‖ ≤ ‖w'‖ + ‖v_s‖ := by
            have heq : (k : ℝ) • a₀ = w' - v_s := by dsimp only [w']; abel
            rw [heq]; exact norm_sub_le w' v_s
          rw [hka_norm] at htri
          have hB_nn : 0 ≤ B_shift := by dsimp only [B_shift]; positivity
          linarith
        have hw'_le : ‖w'‖ ≤ (k : ℝ) * ‖a₀‖ + B_shift := by
          calc
            ‖w'‖ ≤ ‖(k : ℝ) • a₀‖ + ‖v_s‖ := norm_add_le _ _
            _ ≤ (k : ℝ) * ‖a₀‖ + B_shift := by rw [hka_norm]; linarith
        have hw'_in : η_a * ‖w'‖ ≤ inner ℝ e w' := by
          have hvs_in : -B_shift ≤ inner ℝ e v_s := by
            have hn : inner ℝ e (-v_s) ≤ ‖v_s‖ := by
              simpa only [he, one_mul, norm_neg] using real_inner_le_norm e (-v_s)
            rw [inner_neg_right] at hn; linarith
          have hrew : inner ℝ e w' = (k : ℝ) * inner ℝ e a₀ + inner ℝ e v_s := by
            dsimp only [w']; rw [inner_add_right, real_inner_smul_right]
          have hη_prod : η_a * ((k : ℝ) * ‖a₀‖) = ((k : ℝ) * inner ℝ e a₀) / 2 := by
            dsimp only [η_a, α_dir]
            field_simp [ha₀_norm_pos.ne']
          have h1 : η_a * ‖w'‖ ≤ ((k : ℝ) * inner ℝ e a₀) / 2 + η_a * B_shift := by
            have hm := mul_le_mul_of_nonneg_left hw'_le hη_a.1.le
            linarith
          have h2 : η_a * B_shift ≤ B_shift :=
            mul_le_of_le_one_left (by dsimp only [B_shift]; positivity) hη_a.2.le
          rw [hrew]
          linarith
        have hmem := (hR₁_cone (p j + yj) hyj_front w' hw'_ge).1 hw'_in
        have heq_z : (p j + yj) + w' = z := by dsimp only [w', v_s]; abel
        rwa [heq_z] at hmem
      have hc_ep : p j + (y₁ + (k : ℝ) • a₀) ∈ epigraph g :=
        hball_ep (mem_closedBall_self hR_mid.le)
      rw [zeroExtension_of_mem hc_ep]
      exact h.solution_ge_at_ball_center hR_mid ha_mid.1 hball_ep hgap_mid
    rw [(hiter k).2] at ha_le_Vk
    dsimp only [a_mid] at ha_le_Vk
    linarith [hV_lt_one y₁]
  -- Propagate `0 < V_tilde - V` across the preconnected open set `Ω_V`
  have hstrict_all : ∀ y ∈ Ω_V, 0 < V_tilde y - V y := by
    apply positive_of_halfBall_propagation hΩ_open hΩ_conn
      (hVt.continuous.sub hV.continuous).continuousOn hex_strict
    intro c R hR hball hc_pos x hx
    have hlt := hr.pos_on_ball_of_ordered_physical_limits h hR hV hVt hV_val hVt_val
      hlim hVt_lim ha₀_ord hball (sub_pos.mp hc_pos) x
      (ball_subset_ball (half_lt_self hR).le hx)
    exact sub_pos.mpr hlt
  have hstrict_imp : ∀ y, 0 < V y → V y < V (y + a₀) :=
    fun y hy ↦ sub_pos.mp (hstrict_all y hy)
  have hV0_eq : V 0 = 0 := by
    by_contra hne0
    have hp0 : 0 < V 0 := lt_of_le_of_ne (hV_val 0).1 (Ne.symm hne0)
    have hlt0 := hstrict_imp 0 hp0
    rw [zero_add, heq_contact] at hlt0
    exact (lt_irrefl _) hlt0
  exact ⟨hstrict_imp, hV0_eq, heq_contact.trans hV0_eq⟩

end SerrinEpigraph
