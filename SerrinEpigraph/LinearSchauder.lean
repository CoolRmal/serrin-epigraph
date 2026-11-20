module

public import SerrinEpigraph.CampanatoHolder
public import SerrinEpigraph.ConstantCoefficientElliptic

/-!
# Linear Schauder (Campanato) estimates for Lipschitz weak solutions

Weak solutions are tested with Lipschitz functions (`IsWeakDivFree`).

* `caccioppoli`: the Caccioppoli inequality for `div (a ∇z) = div G`;
* `friedrichs_ball`, `setIntegral_norm_sub_setAverage_sq_le`: Friedrichs' inequality and the mean
  as a quasi-best constant;
* `exists_veryWeak_dirichlet`: the Dirichlet problem `L_{A₀} g = div F`, `g = 0` on `∂B`, in the
  very weak sense (minimizing sequence, Rellich compactness);
* `exists_aHarmonic_comparison`: comparison with an `A₀`-harmonic function;
* `excess_decay_of_weakDivFree`, `energy_decay_of_weakDivFree`: Campanato and Morrey decay with a
  right-hand side for constant coefficients;
* `schauder_excess_estimate`: the Campanato estimate for Hölder coefficients, with constants
  depending only on `d, α, ν, Λ, H, R`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Laplacian ContDiff Convolution

namespace SerrinEpigraph

variable {d : ℕ}

/-! ### Lipschitz test functions -/

theorem gradient_eq_zero_of_notMem_tsupport {f : Space d → ℝ} {x : Space d}
    (hx : x ∉ tsupport f) : gradient f x = 0 := by
  simp [gradient, fderiv_of_notMem_tsupport ℝ hx]

/-- A locally Lipschitz function with compact support is globally Lipschitz. -/
theorem LocallyLipschitz.exists_lipschitzWith_of_hasCompactSupport {f : Space d → ℝ}
    (hf : LocallyLipschitz f) (hc : HasCompactSupport f) : ∃ K, LipschitzWith K f := by
  set S := tsupport f with hSdef
  have hS : IsCompact S := hc
  set S' := cthickening 1 S with hS'def
  have hS' : IsCompact S' := hS.cthickening
  obtain ⟨L, hL⟩ := (hf.locallyLipschitzOn (s := S')).exists_lipschitzOnWith_of_compact hS'
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖f x‖ ≤ M := hf.continuous.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set C : NNReal := max L ⟨M, hM0⟩ with hC
  have hLC : (L : ℝ) ≤ C := by exact_mod_cast le_max_left _ _
  have hMC : M ≤ C := by
    have : (⟨M, hM0⟩ : NNReal) ≤ C := le_max_right _ _
    exact_mod_cast this
  have hzero : ∀ x, x ∉ S → f x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hfar : ∀ x ∈ S, ∀ y, y ∉ S' → 1 < dist x y := by
    intro x hx y hy
    by_contra hc'
    exact hy (mem_cthickening_of_dist_le y x 1 S hx (by rw [dist_comm]; exact not_lt.mp hc'))
  have hcross : ∀ x ∈ S, ∀ y, y ∉ S' → dist (f x) (f y) ≤ C * dist x y := by
    intro x hx y hy
    have h1 := hfar x hx y hy
    have hyS : y ∉ S := fun h ↦ hy (self_subset_cthickening S h)
    rw [hzero y hyS, dist_zero_right]
    calc ‖f x‖ ≤ M := hM x
      _ ≤ C * 1 := by rw [mul_one]; exact hMC
      _ ≤ C * dist x y := mul_le_mul_of_nonneg_left h1.le (NNReal.coe_nonneg C)
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  by_cases hx : x ∈ S'
  · by_cases hy : y ∈ S'
    · exact (hL.dist_le_mul x hx y hy).trans
        (mul_le_mul_of_nonneg_right hLC dist_nonneg)
    · by_cases hxS : x ∈ S
      · exact hcross x hxS y hy
      · have hyS : y ∉ S := fun h ↦ hy (self_subset_cthickening S h)
        rw [hzero x hxS, hzero y hyS, dist_self]
        positivity
  · by_cases hyS : y ∈ S
    · rw [dist_comm, dist_comm x]
      exact hcross y hyS x hx
    · have hxS : x ∉ S := fun h ↦ hx (self_subset_cthickening S h)
      rw [hzero x hxS, hzero y hyS, dist_self]
      positivity

/-- A Lipschitz function with compact support has derivatives of zero total integral. -/
theorem integral_fderiv_apply_eq_zero_of_lipschitz {ψ : Space d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) (hc : HasCompactSupport ψ) (v : Space d) :
    ∫ y, fderiv ℝ ψ y v = 0 := by
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_ball (0 : Space d)
  set R := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : tsupport ψ ⊆ ball 0 R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  let χ : ContDiffBump (0 : Space d) := ⟨R, R + 1, hR, by linarith⟩
  have h := integral_fderiv_apply_mul_eq_neg_of_lipschitz hψ (χ.contDiff (n := 1))
    χ.hasCompactSupport v
  have h1 : ∀ y, fderiv ℝ ψ y v * χ y = fderiv ℝ ψ y v := by
    intro y
    by_cases hy : y ∈ tsupport ψ
    · rw [χ.one_of_mem_closedBall (ball_subset_closedBall (hsub hy)), mul_one]
    · simp [fderiv_of_notMem_tsupport ℝ hy]
  have h2 : ∀ y, ψ y * fderiv ℝ χ y v = 0 := by
    intro y
    by_cases hy : y ∈ tsupport ψ
    · have hev : (χ : Space d → ℝ) =ᶠ[𝓝 y] fun _ ↦ 1 := by
        filter_upwards [isOpen_ball.mem_nhds (hsub hy)] with z hz
        exact χ.one_of_mem_closedBall (ball_subset_closedBall hz)
      rw [hev.fderiv_eq]
      simp
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  simp_rw [h1, h2, integral_zero, neg_zero] at h
  exact h

/-- Constant vector fields are weakly divergence free. -/
theorem integral_inner_const_gradient_eq_zero {ψ : Space d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) (hc : HasCompactSupport ψ) (c : Space d) :
    ∫ y, inner ℝ c (gradient ψ y) = 0 := by
  have h : ∀ y, inner ℝ c (gradient ψ y) = fderiv ℝ ψ y c := fun y ↦ by
    rw [inner_gradient_right, conj_trivial]
  simp_rw [h]
  exact integral_fderiv_apply_eq_zero_of_lipschitz hψ hc c

/-! ### Mollification of Lipschitz test functions -/

theorem norm_fderiv_mollify_le {v : Space d → ℝ} {K : NNReal} (hv : LipschitzWith K v)
    (n : ℕ) (x : Space d) : ‖fderiv ℝ (mollify v n) x‖ ≤ K := by
  rw [(mollify_hasFDerivAt_of_lipschitz hv n x).fderiv, convolution_lsmul]
  set k := (averagingBump d n).normed volume with hk
  have hki : Integrable k := (averagingBump d n).integrable_normed
  calc ‖∫ t, k t • fderiv ℝ v (x - t)‖ ≤ ∫ t, k t * K := by
        apply norm_integral_le_of_norm_le (hki.mul_const _)
        filter_upwards with t
        rw [norm_smul, Real.norm_of_nonneg ((averagingBump d n).nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hv)
          ((averagingBump d n).nonneg_normed t)
    _ = K := by rw [integral_mul_const, (averagingBump d n).integral_normed, one_mul]

theorem tsupport_mollify_subset (v : Space d → ℝ) (n : ℕ) :
    tsupport (mollify v n) ⊆ cthickening (1 / ((n : ℝ) + 1)) (tsupport v) := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  have h1 := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (f := (averagingBump d n).normed volume) (g := v) hx
  rw [ContDiffBump.support_normed_eq] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  apply mem_cthickening_of_dist_le _ b _ _ (subset_tsupport v hb)
  rw [dist_eq_norm, add_sub_cancel_right]
  have ha' : ‖a‖ < (averagingBump d n).rOut := by simpa using ha
  exact ha'.le

/-- **Smooth tests suffice**: if a locally integrable vector field is weakly divergence free
against smooth compactly supported tests, then also against Lipschitz ones. -/
theorem integral_inner_gradient_eq_zero_of_lipschitz {U : Set (Space d)} (hU : IsOpen U)
    {V : Space d → Space d} (hV : LocallyIntegrableOn V U)
    (hsmooth : ∀ φ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∫ x, inner ℝ (V x) (gradient φ x) = 0)
    {ψ : Space d → ℝ} {K : NNReal} (hψ : LipschitzWith K ψ) (hc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) : ∫ x, inner ℝ (V x) (gradient ψ x) = 0 := by
  obtain ⟨δ, hδ, hδU⟩ := hc.isCompact.exists_cthickening_subset_open hU hψU
  set S' := cthickening δ (tsupport ψ) with hS'def
  have hS' : IsCompact S' := hc.isCompact.cthickening
  have hVi : IntegrableOn V S' := hV.integrableOn_compact_subset hδU hS'
  have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ δ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 / δ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hsupp : ∀ᶠ n : ℕ in atTop, tsupport (mollify ψ n) ⊆ S' :=
    hev.mono fun n hn ↦ (tsupport_mollify_subset ψ n).trans (cthickening_mono hn _)
  have hset : ∀ f : Space d → ℝ, tsupport f ⊆ S' →
      ∫ x, inner ℝ (V x) (gradient f x) = ∫ x in S', inner ℝ (V x) (gradient f x) := by
    intro f hf
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [gradient_eq_zero_of_notMem_tsupport (fun h ↦ hx (hf h)), inner_zero_right]
  have hψS' : tsupport ψ ⊆ S' := self_subset_cthickening _
  have hzero : ∀ᶠ n : ℕ in atTop, ∫ x in S', inner ℝ (V x) (gradient (mollify ψ n) x) = 0 :=
    hsupp.mono fun n hn ↦ by
      rw [← hset _ hn]
      exact hsmooth _ (mollify_contDiff hψ.continuous n)
        (hS'.of_isClosed_subset (isClosed_tsupport _) hn) (hn.trans hδU)
  have hlim : Tendsto (fun n ↦ ∫ x in S', inner ℝ (V x) (gradient (mollify ψ n) x)) atTop
      (𝓝 (∫ x in S', inner ℝ (V x) (gradient ψ x))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖V x‖ * K)
    · exact Eventually.of_forall fun n ↦ hVi.aestronglyMeasurable.inner
        ((toDual ℝ (Space d)).symm.continuous.comp
          ((mollify_contDiff hψ.continuous n).continuous_fderiv
            (by simp))).aestronglyMeasurable
    · refine Eventually.of_forall fun n ↦ Eventually.of_forall fun x ↦ ?_
      calc ‖inner ℝ (V x) (gradient (mollify ψ n) x)‖
          ≤ ‖V x‖ * ‖gradient (mollify ψ n) x‖ := norm_inner_le_norm _ _
        _ ≤ ‖V x‖ * K := by
            gcongr
            rw [gradient, LinearIsometryEquiv.norm_map]
            exact norm_fderiv_mollify_le hψ n x
    · exact hVi.norm.mul_const _
    · filter_upwards [ae_restrict_of_ae (mollify_fderiv_tendsto_ae_of_lipschitz hψ)] with x hx
      have h1 := ((toDual ℝ (Space d)).symm.continuous.tendsto (fderiv ℝ ψ x)).comp hx
      exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp h1
  rw [hset ψ hψS']
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun n hn ↦ hn.symm))

/-- `div V = 0` weakly in `U`, tested with Lipschitz functions compactly supported in `U`. -/
def IsWeakDivFree (V : Space d → Space d) (U : Set (Space d)) : Prop :=
  ∀ ψ : Space d → ℝ, (∃ K, LipschitzWith K ψ) → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∫ x, inner ℝ (V x) (gradient ψ x) = 0

theorem IsWeakDivFree.of_smooth {U : Set (Space d)} (hU : IsOpen U) {V : Space d → Space d}
    (hV : LocallyIntegrableOn V U)
    (hsmooth : ∀ φ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∫ x, inner ℝ (V x) (gradient φ x) = 0) :
    IsWeakDivFree V U := fun _ ⟨_, hψ⟩ hc hψU ↦
  integral_inner_gradient_eq_zero_of_lipschitz hU hV hsmooth hψ hc hψU

theorem IsWeakDivFree.mono {V : Space d → Space d} {U U' : Set (Space d)}
    (h : IsWeakDivFree V U) (hU' : U' ⊆ U) : IsWeakDivFree V U' :=
  fun ψ hψ hc hs ↦ h ψ hψ hc (hs.trans hU')


/-! ### A Lipschitz radial cutoff -/

/-- The radial cutoff: `1` on `closedBall x₀ ρ`, `0` outside `ball x₀ ((ρ + s) / 2)`, and
`2 / (s - ρ)`-Lipschitz. -/
def radialCutoff (x₀ : Space d) (ρ s : ℝ) (y : Space d) : ℝ :=
  min 1 (max 0 (((ρ + s) / 2 - dist y x₀) / ((s - ρ) / 2)))

section Cutoff

variable {x₀ : Space d} {ρ s : ℝ}

theorem radialCutoff_lipschitzWith (hρs : ρ < s) :
    LipschitzWith ⟨2 / (s - ρ), (div_pos two_pos (sub_pos.2 hρs)).le⟩
      (radialCutoff x₀ ρ s) := by
  have hsr : 0 < s - ρ := sub_pos.2 hρs
  have h1 : LipschitzWith ⟨2 / (s - ρ), (div_pos two_pos hsr).le⟩
      (fun y : Space d ↦ ((ρ + s) / 2 - dist y x₀) / ((s - ρ) / 2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Real.dist_eq]
    have he : ((ρ + s) / 2 - dist y x₀) / ((s - ρ) / 2) -
        ((ρ + s) / 2 - dist z x₀) / ((s - ρ) / 2) = 2 / (s - ρ) * (dist z x₀ - dist y x₀) := by
      field_simp
      ring
    rw [he, abs_mul, abs_of_pos (div_pos two_pos hsr)]
    have h2 : |dist z x₀ - dist y x₀| ≤ dist y z := by
      rw [dist_comm y z]
      exact abs_dist_sub_le z y x₀
    exact mul_le_mul_of_nonneg_left h2 (div_pos two_pos hsr).le
  exact (h1.const_max 0).const_min 1

theorem radialCutoff_nonneg (y : Space d) : 0 ≤ radialCutoff x₀ ρ s y :=
  le_min zero_le_one (le_max_left _ _)

theorem radialCutoff_le_one (y : Space d) : radialCutoff x₀ ρ s y ≤ 1 :=
  min_le_left _ _

theorem radialCutoff_eq_one (hρs : ρ < s) {y : Space d} (hy : dist y x₀ ≤ ρ) :
    radialCutoff x₀ ρ s y = 1 := by
  have hsr : 0 < (s - ρ) / 2 := by linarith
  have h1 : 1 ≤ ((ρ + s) / 2 - dist y x₀) / ((s - ρ) / 2) := by
    rw [le_div_iff₀ hsr]
    linarith
  unfold radialCutoff
  rw [max_eq_right (by linarith), min_eq_left h1]

theorem radialCutoff_eq_zero (hρs : ρ < s) {y : Space d} (hy : (ρ + s) / 2 ≤ dist y x₀) :
    radialCutoff x₀ ρ s y = 0 := by
  have h1 : ((ρ + s) / 2 - dist y x₀) / ((s - ρ) / 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  unfold radialCutoff
  rw [max_eq_left h1, min_eq_right zero_le_one]

theorem tsupport_radialCutoff_subset (hρs : ρ < s) :
    tsupport (radialCutoff x₀ ρ s) ⊆ closedBall x₀ ((ρ + s) / 2) := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  by_contra hc
  apply hy
  apply radialCutoff_eq_zero hρs
  simp only [mem_closedBall, not_le] at hc
  exact hc.le

end Cutoff

/-- A product `η z` with `|η| ≤ 1` Lipschitz and vanishing off a compact set and `z` Lipschitz
is Lipschitz. -/
theorem exists_lipschitzWith_mul_of_compact {η z : Space d → ℝ} {Lη Lz : NNReal}
    (hη : LipschitzWith Lη η) (hz : LipschitzWith Lz z) {B : Set (Space d)} (hB : IsCompact B)
    (hηB : ∀ x, x ∉ B → η x = 0) (hη1 : ∀ x, |η x| ≤ 1) :
    ∃ K, LipschitzWith K (fun x ↦ η x * z x) := by
  obtain ⟨Z, hZ⟩ := hB.exists_bound_of_continuousOn hz.continuous.continuousOn
  set Z' := max Z 0 with hZ'
  have hZ'0 : 0 ≤ Z' := le_max_right _ _
  have key : ∀ x y, x ∈ B →
      dist (η x * z x) (η y * z y) ≤ (Lη * Z' + Lz) * dist x y := by
    intro x y hx
    rw [Real.dist_eq]
    have e : η x * z x - η y * z y = (η x - η y) * z x + η y * (z x - z y) := by ring
    have h1 : |η x - η y| ≤ Lη * dist x y := by
      rw [← Real.dist_eq]
      exact hη.dist_le_mul x y
    have h2 : |z x - z y| ≤ Lz * dist x y := by
      rw [← Real.dist_eq]
      exact hz.dist_le_mul x y
    have h3 : |z x| ≤ Z' := by
      rw [← Real.norm_eq_abs]
      exact (hZ x hx).trans (le_max_left _ _)
    rw [e]
    calc |(η x - η y) * z x + η y * (z x - z y)|
        ≤ |(η x - η y) * z x| + |η y * (z x - z y)| := abs_add_le _ _
      _ = |η x - η y| * |z x| + |η y| * |z x - z y| := by rw [abs_mul, abs_mul]
      _ ≤ (Lη * dist x y) * Z' + 1 * (Lz * dist x y) := by
          gcongr
          exact hη1 y
      _ = (Lη * Z' + Lz) * dist x y := by ring
  refine ⟨Lη * Z'.toNNReal + Lz, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have hcoe : ((Lη * Z'.toNNReal + Lz : NNReal) : ℝ) = Lη * Z' + Lz := by
    rw [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ hZ'0]
  rw [hcoe]
  by_cases hx : x ∈ B
  · exact key x y hx
  · by_cases hy : y ∈ B
    · rw [dist_comm, dist_comm x]
      exact key y x hy
    · simp only [hηB x hx, hηB y hy, zero_mul, dist_self]
      positivity

/-! ### Caccioppoli inequality -/

/-- The pointwise algebra behind the Caccioppoli inequality. -/
theorem caccioppoli_pointwise {ν Λ : ℝ} (hν : 0 < ν) {A : Space d →L[ℝ] Space d}
    (hA : ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) (hAb : ‖A‖ ≤ Λ) (E Z : ℝ) (P Q F : Space d) :
    ν / 2 * (E ^ 2 * ‖P‖ ^ 2) - (4 * Λ ^ 2 / ν + 1) * (Z ^ 2 * ‖Q‖ ^ 2) -
        (1 / ν + 1) * (E ^ 2 * ‖F‖ ^ 2) ≤
      inner ℝ (A P - F) (E ^ 2 • P + (2 * E * Z) • Q) := by
  have e1 : inner ℝ (A P - F) (E ^ 2 • P + (2 * E * Z) • Q) =
      E ^ 2 * inner ℝ (A P) P + 2 * E * Z * inner ℝ (A P) Q - E ^ 2 * inner ℝ F P -
        2 * E * Z * inner ℝ F Q := by
    simp only [inner_add_right, inner_sub_left, real_inner_smul_right]
    ring
  rw [e1]
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hAb
  set p := ‖P‖ with hp
  set q := ‖Q‖ with hq
  set f := ‖F‖ with hf
  have hp0 : 0 ≤ p := norm_nonneg _
  have hq0 : 0 ≤ q := norm_nonneg _
  have hf0 : 0 ≤ f := norm_nonneg _
  have h1 := hA P
  have hAP : ‖A P‖ ≤ Λ * p :=
    (A.le_opNorm P).trans (mul_le_mul_of_nonneg_right hAb (norm_nonneg _))
  have h2 : |inner ℝ (A P) Q| ≤ Λ * p * q :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hAP (norm_nonneg _))
  have h3 : |inner ℝ F P| ≤ f * p := abs_real_inner_le_norm _ _
  have h4 : |inner ℝ F Q| ≤ f * q := abs_real_inner_le_norm _ _
  set e := |E| with he
  set z := |Z| with hz
  have he0 : 0 ≤ e := abs_nonneg _
  have hz0 : 0 ≤ z := abs_nonneg _
  have hE2 : E ^ 2 = e ^ 2 := (sq_abs E).symm
  have hZ2 : Z ^ 2 = z ^ 2 := (sq_abs Z).symm
  have hEZ : |2 * E * Z| = 2 * e * z := by
    rw [abs_mul, abs_mul, abs_two]
  -- three Young inequalities
  have t1 : -(2 * E * Z * inner ℝ (A P) Q) ≤
      ν / 4 * (e ^ 2 * p ^ 2) + 4 * Λ ^ 2 / ν * (z ^ 2 * q ^ 2) := by
    have hb : |2 * E * Z * inner ℝ (A P) Q| ≤ 2 * e * z * (Λ * p * q) := by
      rw [abs_mul, hEZ]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have hsq : 0 ≤ ν / 4 * (e * p - 4 * Λ / ν * (z * q)) ^ 2 := by positivity
    have hexp : ν / 4 * (e * p - 4 * Λ / ν * (z * q)) ^ 2 =
        ν / 4 * (e ^ 2 * p ^ 2) + 4 * Λ ^ 2 / ν * (z ^ 2 * q ^ 2) - 2 * e * z * (Λ * p * q) := by
      field_simp
      ring
    linarith [neg_abs_le (2 * E * Z * inner ℝ (A P) Q)]
  have t2 : E ^ 2 * inner ℝ F P ≤ ν / 4 * (e ^ 2 * p ^ 2) + 1 / ν * (e ^ 2 * f ^ 2) := by
    have hb : E ^ 2 * inner ℝ F P ≤ e ^ 2 * (f * p) := by
      rw [hE2]
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans h3) (by positivity)
    have hsq : 0 ≤ ν / 4 * (e * p - 2 / ν * (e * f)) ^ 2 := by positivity
    have hexp : ν / 4 * (e * p - 2 / ν * (e * f)) ^ 2 =
        ν / 4 * (e ^ 2 * p ^ 2) + 1 / ν * (e ^ 2 * f ^ 2) - e ^ 2 * (f * p) := by
      field_simp
      ring
    linarith
  have t3 : 2 * E * Z * inner ℝ F Q ≤ e ^ 2 * f ^ 2 + z ^ 2 * q ^ 2 := by
    have hb : 2 * E * Z * inner ℝ F Q ≤ 2 * e * z * (f * q) := by
      calc 2 * E * Z * inner ℝ F Q ≤ |2 * E * Z * inner ℝ F Q| := le_abs_self _
        _ = 2 * e * z * |inner ℝ F Q| := by rw [abs_mul, hEZ]
        _ ≤ 2 * e * z * (f * q) := mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith [sq_nonneg (e * f - z * q)]
  have t0 : ν * (e ^ 2 * p ^ 2) ≤ E ^ 2 * inner ℝ (A P) P := by
    rw [hE2]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg e)]
  rw [hE2, hZ2]
  rw [hE2] at t2
  nlinarith [t0, t1, t2, t3]

theorem caccioppoli {a : Space d → Space d →L[ℝ] Space d} {ν Λ : ℝ} (hν : 0 < ν)
    {x₀ : Space d} {ρ s : ℝ} (hρs : ρ < s)
    (ha : AEStronglyMeasurable a (volume.restrict (ball x₀ s)))
    (hell : ∀ y ∈ ball x₀ s, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a y ξ) ξ)
    (hbd : ∀ y ∈ ball x₀ s, ‖a y‖ ≤ Λ)
    {G : Space d → Space d} (hG : MemLp G 2 (volume.restrict (ball x₀ s)))
    {z : Space d → ℝ} {K : NNReal} (hz : LipschitzWith K z)
    (heq : IsWeakDivFree (fun y ↦ a y (gradient z y) - G y) (ball x₀ s)) :
    ∫ y in ball x₀ ρ, ‖gradient z y‖ ^ 2 ≤
      2 / ν * ((4 * Λ ^ 2 / ν + 1) * (2 / (s - ρ)) ^ 2 * (∫ y in ball x₀ s, z y ^ 2) +
        (1 / ν + 1) * ∫ y in ball x₀ s, ‖G y‖ ^ 2) := by
  have hsρ : 0 < s - ρ := sub_pos.2 hρs
  set η := radialCutoff x₀ ρ s with hηdef
  set Lη : NNReal := ⟨2 / (s - ρ), (div_pos two_pos hsρ).le⟩ with hLη
  have hη : LipschitzWith Lη η := radialCutoff_lipschitzWith hρs
  have hηsub : tsupport η ⊆ ball x₀ s :=
    (tsupport_radialCutoff_subset hρs).trans (closedBall_subset_ball (by linarith))
  have hηzero : ∀ y, y ∉ ball x₀ s → η y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hηsub h))
  have hηabs : ∀ y, |η y| ≤ 1 := fun y ↦ by
    rw [abs_of_nonneg (radialCutoff_nonneg y)]
    exact radialCutoff_le_one y
  have hηzero' : ∀ y, y ∉ closedBall x₀ s → η y = 0 := fun y hy ↦
    hηzero y (fun h ↦ hy (ball_subset_closedBall h))
  set ψ : Space d → ℝ := fun y ↦ η y ^ 2 * z y with hψdef
  have hψlip : ∃ K', LipschitzWith K' ψ := by
    obtain ⟨K₁, hK₁⟩ := exists_lipschitzWith_mul_of_compact hη hz (isCompact_closedBall x₀ s)
      hηzero' hηabs
    obtain ⟨K₂, hK₂⟩ := exists_lipschitzWith_mul_of_compact hη hK₁ (isCompact_closedBall x₀ s)
      hηzero' hηabs
    refine ⟨K₂, ?_⟩
    have he : (fun x ↦ η x * (η x * z x)) = ψ := by
      funext x
      simp only [hψdef]
      ring
    rw [← he]
    exact hK₂
  have hψsub : tsupport ψ ⊆ ball x₀ s := by
    have h1 : Function.support ψ ⊆ Function.support η := by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hη0
      apply hy
      simp [hψdef, hη0]
    exact (closure_mono h1).trans hηsub
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall x₀ s).of_isClosed_subset (isClosed_tsupport _)
      (hψsub.trans ball_subset_closedBall)
  have h0 := heq ψ hψlip hψc hψsub
  have hgrad : ∀ᵐ y, gradient ψ y =
      (η y ^ 2) • gradient z y + (2 * η y * z y) • gradient η y := by
    filter_upwards [hz.ae_differentiableAt (μ := volume),
      hη.ae_differentiableAt (μ := volume)] with y hzy hηy
    have hd := (hηy.hasFDerivAt.pow 2).mul hzy.hasFDerivAt
    have hd' : HasFDerivAt ψ ((η y ^ 2) • fderiv ℝ z y + (2 * η y * z y) • fderiv ℝ η y) y := by
      convert hd using 1
      ext v
      simp
      ring
    rw [gradient, hd'.fderiv, map_add, map_smul, map_smul]
    rfl
  have hgη : ∀ y, ‖gradient η y‖ ≤ 2 / (s - ρ) := fun y ↦ by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hη
  have hgη0 : ∀ y, y ∉ ball x₀ s → gradient η y = 0 := fun y hy ↦
    gradient_eq_zero_of_notMem_tsupport (fun h ↦ hy (hηsub h))
  have hgψ0 : ∀ y, y ∉ ball x₀ s → gradient ψ y = 0 := fun y hy ↦
    gradient_eq_zero_of_notMem_tsupport (fun h ↦ hy (hψsub h))
  have hgz : ∀ y, ‖gradient z y‖ ≤ K := fun y ↦ by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hz
  set c₁ := 4 * Λ ^ 2 / ν + 1 with hc₁
  set c₂ := 1 / ν + 1 with hc₂
  set lhs : Space d → ℝ := fun y ↦ ν / 2 * (η y ^ 2 * ‖gradient z y‖ ^ 2) -
    c₁ * (z y ^ 2 * ‖gradient η y‖ ^ 2) - c₂ * (η y ^ 2 * ‖G y‖ ^ 2) with hlhs
  set rhs : Space d → ℝ := fun y ↦ inner ℝ (a y (gradient z y) - G y) (gradient ψ y) with hrhs
  have hpt : ∀ᵐ y ∂(volume.restrict (ball x₀ s)), lhs y ≤ rhs y := by
    filter_upwards [ae_restrict_of_ae hgrad, ae_restrict_mem measurableSet_ball] with y hy hyB
    simp only [hrhs, hlhs]
    rw [hy]
    exact caccioppoli_pointwise hν (hell y hyB) (hbd y hyB) _ _ _ _ _
  -- reduce to integrals over the ball
  have hrhs0 : ∫ y, rhs y = ∫ y in ball x₀ s, rhs y := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    show inner ℝ (a y (gradient z y) - G y) (gradient ψ y) = 0
    rw [hgψ0 y hy, inner_zero_right]
  -- measurability and bounds on the ball
  have hfin : volume (ball x₀ s) ≠ ⊤ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball x₀ s)) := isFiniteMeasure_restrict.2 hfin
  obtain ⟨Z, hZ⟩ := (isCompact_closedBall x₀ s).exists_bound_of_continuousOn
    hz.continuous.continuousOn
  have hgradm : Measurable (fun y ↦ gradient z y) :=
    (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ z)
  have hgradηm : Measurable (fun y ↦ gradient η y) :=
    (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ η)
  have hgradψm : Measurable (fun y ↦ gradient ψ y) :=
    (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ ψ)
  have hGm : AEStronglyMeasurable G (volume.restrict (ball x₀ s)) := hG.aestronglyMeasurable
  have hG2 : Integrable (fun y ↦ ‖G y‖ ^ 2) (volume.restrict (ball x₀ s)) := hG.norm.integrable_sq
  have hG1 : Integrable G (volume.restrict (ball x₀ s)) := hG.integrable one_le_two
  obtain ⟨Kψ, hKψ⟩ := hψlip
  have hgψ : ∀ y, ‖gradient ψ y‖ ≤ Kψ := fun y ↦ by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hKψ
  have hint_rhs : Integrable rhs (volume.restrict (ball x₀ s)) := by
    have hbnd : Integrable (fun y ↦ (Λ * K + ‖G y‖) * Kψ) (volume.restrict (ball x₀ s)) :=
      ((integrable_const _).add hG1.norm).mul_const _
    refine hbnd.mono' ?_ ?_
    · have hm : AEStronglyMeasurable (fun y ↦ a y (gradient z y))
          (volume.restrict (ball x₀ s)) :=
        (ContinuousLinearMap.id ℝ (Space d →L[ℝ] Space d)).aestronglyMeasurable_comp₂
          ha hgradm.aestronglyMeasurable
      exact (hm.sub hGm).inner hgradψm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hyB
      have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hbd y hyB)
      have h1 : ‖a y (gradient z y) - G y‖ ≤ Λ * K + ‖G y‖ :=
        (norm_sub_le _ _).trans (add_le_add
          (((a y).le_opNorm _).trans (mul_le_mul (hbd y hyB) (hgz y) (norm_nonneg _) hΛ0)) le_rfl)
      calc ‖rhs y‖ ≤ ‖a y (gradient z y) - G y‖ * ‖gradient ψ y‖ := norm_inner_le_norm _ _
        _ ≤ (Λ * K + ‖G y‖) * Kψ := mul_le_mul h1 (hgψ y) (norm_nonneg _) (by positivity)
  have hint1 : Integrable (fun y ↦ η y ^ 2 * ‖gradient z y‖ ^ 2) (volume.restrict (ball x₀ s)) :=
    Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) hfin
      ((hη.continuous.pow 2).aestronglyMeasurable.mul
        (hgradm.norm.pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        have h1 : η y ^ 2 ≤ 1 := by
          rw [← sq_abs]
          exact pow_le_one₀ (abs_nonneg _) (hηabs y)
        calc η y ^ 2 * ‖gradient z y‖ ^ 2 ≤ 1 * (K : ℝ) ^ 2 := mul_le_mul h1
              (pow_le_pow_left₀ (norm_nonneg _) (hgz y) 2) (by positivity) zero_le_one
          _ = (K : ℝ) ^ 2 := one_mul _)
  have hint2 : Integrable (fun y ↦ z y ^ 2 * ‖gradient η y‖ ^ 2) (volume.restrict (ball x₀ s)) := by
    refine Measure.integrableOn_of_bounded (M := Z ^ 2 * (2 / (s - ρ)) ^ 2) hfin
      ((hz.continuous.pow 2).aestronglyMeasurable.mul
        (hgradηm.norm.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hyB
    rw [Real.norm_of_nonneg (by positivity)]
    have hzy : |z y| ≤ Z := by
      rw [← Real.norm_eq_abs]
      exact hZ y (ball_subset_closedBall hyB)
    exact mul_le_mul (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hzy 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hgη y) 2) (by positivity) (sq_nonneg Z)
  have hint3 : Integrable (fun y ↦ η y ^ 2 * ‖G y‖ ^ 2) (volume.restrict (ball x₀ s)) := by
    refine hG2.bdd_mul (c := 1) (hη.continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity), ← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (hηabs y)
  have hint_lhs : Integrable lhs (volume.restrict (ball x₀ s)) :=
    ((hint1.const_mul _).sub (hint2.const_mul _)).sub (hint3.const_mul _)
  have hle := integral_mono_ae hint_lhs hint_rhs hpt
  rw [← hrhs0] at hle
  change ∫ y in ball x₀ s, lhs y ≤ ∫ y, inner ℝ (a y (gradient z y) - G y) (gradient ψ y) at hle
  rw [h0] at hle
  have hexp : ∫ y in ball x₀ s, lhs y =
      ν / 2 * (∫ y in ball x₀ s, η y ^ 2 * ‖gradient z y‖ ^ 2) -
        c₁ * (∫ y in ball x₀ s, z y ^ 2 * ‖gradient η y‖ ^ 2) -
          c₂ * ∫ y in ball x₀ s, η y ^ 2 * ‖G y‖ ^ 2 := by
    have i1 : Integrable (fun y ↦ ν / 2 * (η y ^ 2 * ‖gradient z y‖ ^ 2))
        (volume.restrict (ball x₀ s)) := hint1.const_mul _
    have i2 : Integrable (fun y ↦ c₁ * (z y ^ 2 * ‖gradient η y‖ ^ 2))
        (volume.restrict (ball x₀ s)) := hint2.const_mul _
    have i3 : Integrable (fun y ↦ c₂ * (η y ^ 2 * ‖G y‖ ^ 2))
        (volume.restrict (ball x₀ s)) := hint3.const_mul _
    have i12 : Integrable (fun y ↦ ν / 2 * (η y ^ 2 * ‖gradient z y‖ ^ 2) -
        c₁ * (z y ^ 2 * ‖gradient η y‖ ^ 2)) (volume.restrict (ball x₀ s)) := i1.sub i2
    have e1 := integral_sub i12 i3
    have e2 := integral_sub i1 i2
    simp only [hlhs]
    rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hexp] at hle
  -- the three comparisons
  have hA : ∫ y in ball x₀ ρ, ‖gradient z y‖ ^ 2 ≤
      ∫ y in ball x₀ s, η y ^ 2 * ‖gradient z y‖ ^ 2 := by
    have hρsub : ball x₀ ρ ⊆ ball x₀ s := ball_subset_ball hρs.le
    calc ∫ y in ball x₀ ρ, ‖gradient z y‖ ^ 2 =
          ∫ y in ball x₀ ρ, η y ^ 2 * ‖gradient z y‖ ^ 2 := by
          apply setIntegral_congr_fun measurableSet_ball
          intro y hy
          have h1 : η y = 1 := radialCutoff_eq_one hρs (mem_ball.1 hy).le
          simp only
          rw [h1, one_pow, one_mul]
      _ ≤ ∫ y in ball x₀ s, η y ^ 2 * ‖gradient z y‖ ^ 2 :=
          setIntegral_mono_set hint1 (Eventually.of_forall fun y ↦ by positivity)
            hρsub.eventuallyLE
  have hB : ∫ y in ball x₀ s, z y ^ 2 * ‖gradient η y‖ ^ 2 ≤
      (2 / (s - ρ)) ^ 2 * ∫ y in ball x₀ s, z y ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall fun y ↦ by positivity)
      ((hz.continuous.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall x₀ s)
        |>.mono_set ball_subset_closedBall |>.const_mul _)
    filter_upwards with y
    rw [mul_comm ((2 / (s - ρ)) ^ 2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hgη y) 2) (sq_nonneg _)
  have hC : ∫ y in ball x₀ s, η y ^ 2 * ‖G y‖ ^ 2 ≤ ∫ y in ball x₀ s, ‖G y‖ ^ 2 := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun y ↦ by positivity) hG2
    filter_upwards with y
    have h1 : η y ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (hηabs y)
    calc η y ^ 2 * ‖G y‖ ^ 2 ≤ 1 * ‖G y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖G y‖ ^ 2 := one_mul _
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hmain : ν / 2 * (∫ y in ball x₀ s, η y ^ 2 * ‖gradient z y‖ ^ 2) ≤
      c₁ * ((2 / (s - ρ)) ^ 2 * ∫ y in ball x₀ s, z y ^ 2) +
        c₂ * ∫ y in ball x₀ s, ‖G y‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hB hc₁0, mul_le_mul_of_nonneg_left hC hc₂0]
  have hfinal : ∫ y in ball x₀ s, η y ^ 2 * ‖gradient z y‖ ^ 2 ≤
      2 / ν * (c₁ * (2 / (s - ρ)) ^ 2 * (∫ y in ball x₀ s, z y ^ 2) +
        c₂ * ∫ y in ball x₀ s, ‖G y‖ ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hν]
    nlinarith [hmain]
  exact hA.trans hfinal

/-! ### Volumes of balls, Friedrichs' inequality, and the mean as best constant -/

theorem measureReal_ball_eq_mul (x : Space d) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) = r ^ d * volume.real (ball (0 : Space d) 1) := by
  rw [measureReal_def, measureReal_def, Measure.addHaar_ball_of_pos volume x hr,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem measureReal_unitBall_pos : 0 < volume.real (ball (0 : Space d) 1) :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/-- The constant `6 · 2^(d+1) · 4` of Friedrichs' inequality on balls. -/
def friedrichsConst (d : ℕ) : ℝ := 24 * 2 ^ (d + 1)

theorem friedrichsConst_nonneg (d : ℕ) : 0 ≤ friedrichsConst d := by
  unfold friedrichsConst; positivity

/-- **Friedrichs' inequality**: a Lipschitz function supported in a ball `B_r` satisfies
`∫_{B_r} ψ² ≤ C r² ∫_{B_r} ‖Dψ‖²`. -/
theorem friedrichs_ball (hd : 0 < d) (x : Space d) {r : ℝ} (hr : 0 < r) {ψ : Space d → ℝ}
    {K : NNReal} (hψ : LipschitzWith K ψ) (hsupp : tsupport ψ ⊆ ball x r) :
    ∫ y in ball x r, ψ y ^ 2 ≤
      friedrichsConst d * r ^ 2 * ∫ y in ball x r, ‖fderiv ℝ ψ y‖ ^ 2 := by
  have hr2 : 0 < 2 * r := by positivity
  have hsub : ball x r ⊆ ball x (2 * r) := ball_subset_ball (by linarith)
  have hzero : ∀ y, y ∉ ball x r → ψ y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hsupp h))
  have hdzero : ∀ y, y ∉ ball x r → fderiv ℝ ψ y = 0 := fun y hy ↦
    fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hsupp h))
  have hfin2 : volume (ball x (2 * r)) ≠ ⊤ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball x (2 * r))) := isFiniteMeasure_restrict.2 hfin2
  have hcont2 : ∀ s, IntegrableOn (fun y ↦ ψ y ^ 2) (ball x s) := fun s ↦
    ((hψ.continuous.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall x s)).mono_set
      ball_subset_closedBall
  have hcont1 : ∀ s, IntegrableOn ψ (ball x s) := fun s ↦
    (hψ.continuous.continuousOn.integrableOn_compact (isCompact_closedBall x s)).mono_set
      ball_subset_closedBall
  set a := ⨍ z in ball x (2 * r), ψ z with ha
  have hP := poincare_ball x hr2 hψ
  -- the integrals over `B_{2r}` reduce to `B_r`
  have hD : ∫ y in ball x (2 * r), ‖fderiv ℝ ψ y‖ ^ 2 = ∫ y in ball x r, ‖fderiv ℝ ψ y‖ ^ 2 :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
      (fun y hy ↦ by simp [hdzero y hy.2])
  have hS : ∫ y in ball x (2 * r), ψ y ^ 2 = ∫ y in ball x r, ψ y ^ 2 :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
      (fun y hy ↦ by simp [hzero y hy.2])
  -- the average is controlled on the annulus
  set m₁ := volume.real (ball x r) with hm₁
  set m₂ := volume.real (ball x (2 * r)) with hm₂
  have hm₂eq : m₂ = 2 ^ d * m₁ := by
    rw [hm₂, hm₁, measureReal_ball_eq_mul x hr2, measureReal_ball_eq_mul x hr, mul_pow]
    ring
  have hm₁0 : 0 ≤ m₁ := measureReal_nonneg
  have h2d : (2 : ℝ) ≤ 2 ^ d := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hann : m₂ - m₁ = volume.real (ball x (2 * r) \ ball x r) := by
    rw [measureReal_sdiff hsub measurableSet_ball]
  have hsq_int : IntegrableOn (fun y ↦ (ψ y - a) ^ 2) (ball x (2 * r)) := by
    have h1 : IntegrableOn (fun y ↦ ψ y ^ 2 - 2 * a * ψ y + a ^ 2) (ball x (2 * r)) :=
      ((hcont2 _).sub ((hcont1 _).const_mul _)).add (integrable_const _)
    refine h1.congr (Eventually.of_forall fun y ↦ ?_)
    simp only
    ring
  have hlow : (m₂ - m₁) * a ^ 2 ≤ ∫ y in ball x (2 * r), (ψ y - a) ^ 2 := by
    have h1 : ∫ y in ball x (2 * r) \ ball x r, (ψ y - a) ^ 2 = (m₂ - m₁) * a ^ 2 := by
      rw [hann]
      have : ∫ y in ball x (2 * r) \ ball x r, (ψ y - a) ^ 2 =
          ∫ y in ball x (2 * r) \ ball x r, a ^ 2 := by
        apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
        intro y hy
        simp [hzero y hy.2]
      rw [this, setIntegral_const, smul_eq_mul]
    rw [← h1]
    exact setIntegral_mono_set hsq_int (Eventually.of_forall fun y ↦ sq_nonneg _)
      (sdiff_subset).eventuallyLE
  have hpt : ∫ y in ball x (2 * r), ψ y ^ 2 ≤
      2 * (∫ y in ball x (2 * r), (ψ y - a) ^ 2) + 2 * (m₂ * a ^ 2) := by
    have h1 : ∫ y in ball x (2 * r), ψ y ^ 2 ≤
        ∫ y in ball x (2 * r), (2 * (ψ y - a) ^ 2 + 2 * a ^ 2) := by
      apply integral_mono (hcont2 _) ((hsq_int.const_mul 2).add (integrable_const _))
      intro y
      show ψ y ^ 2 ≤ 2 * (ψ y - a) ^ 2 + 2 * a ^ 2
      nlinarith [sq_nonneg (ψ y - 2 * a)]
    rw [integral_add (hsq_int.const_mul 2) (integrable_const _), integral_const_mul,
      setIntegral_const, smul_eq_mul, ← hm₂] at h1
    calc ∫ y in ball x (2 * r), ψ y ^ 2 ≤
        2 * (∫ y in ball x (2 * r), (ψ y - a) ^ 2) + m₂ * (2 * a ^ 2) := h1
      _ = 2 * (∫ y in ball x (2 * r), (ψ y - a) ^ 2) + 2 * (m₂ * a ^ 2) := by ring
  have hm : m₂ ≤ 2 * (m₂ - m₁) := by
    rw [hm₂eq]
    nlinarith
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have hkey : ∫ y in ball x (2 * r), ψ y ^ 2 ≤ 6 * ∫ y in ball x (2 * r), (ψ y - a) ^ 2 := by
    have h3 : m₂ * a ^ 2 ≤ 2 * ((m₂ - m₁) * a ^ 2) := by nlinarith
    calc ∫ y in ball x (2 * r), ψ y ^ 2 ≤
        2 * (∫ y in ball x (2 * r), (ψ y - a) ^ 2) + 2 * (m₂ * a ^ 2) := hpt
      _ ≤ 2 * (∫ y in ball x (2 * r), (ψ y - a) ^ 2) + 2 * (2 * ((m₂ - m₁) * a ^ 2)) := by
          gcongr
      _ ≤ 2 * (∫ y in ball x (2 * r), (ψ y - a) ^ 2) +
          2 * (2 * ∫ y in ball x (2 * r), (ψ y - a) ^ 2) := by gcongr
      _ = 6 * ∫ y in ball x (2 * r), (ψ y - a) ^ 2 := by ring
  rw [← hS, ← hD]
  calc ∫ y in ball x (2 * r), ψ y ^ 2 ≤ 6 * ∫ y in ball x (2 * r), (ψ y - a) ^ 2 := hkey
    _ ≤ 6 * (2 ^ (d + 1) * (2 * r) ^ 2 * ∫ y in ball x (2 * r), ‖fderiv ℝ ψ y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hP (by norm_num)
    _ = friedrichsConst d * r ^ 2 * ∫ y in ball x (2 * r), ‖fderiv ℝ ψ y‖ ^ 2 := by
        unfold friedrichsConst; ring

/-- The mean is a quasi-best constant in `L²` (in any Banach space):
`∫_S ‖f - f_S‖² ≤ 4 ∫_S ‖f - c‖²`. -/
theorem setIntegral_norm_sub_setAverage_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {S : Set (Space d)} (hSf : volume S ≠ ⊤)
    {f : Space d → E} (hf : MemLp f 2 (volume.restrict S)) (c : E) :
    ∫ y in S, ‖f y - ⨍ z in S, f z‖ ^ 2 ≤ 4 * ∫ y in S, ‖f y - c‖ ^ 2 := by
  by_cases hS0 : volume S = 0
  · simp [Measure.restrict_eq_zero.2 hS0]
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf
  have hm : 0 < volume.real S := ENNReal.toReal_pos hS0 hSf
  set m := volume.real S with hmdef
  set av := ⨍ z in S, f z with hav
  have hfi : Integrable f (volume.restrict S) := hf.integrable one_le_two
  have hfc : MemLp (fun y ↦ f y - c) 2 (volume.restrict S) := hf.sub (memLp_const c)
  have hfc2 : Integrable (fun y ↦ ‖f y - c‖ ^ 2) (volume.restrict S) := hfc.norm.integrable_sq
  have hfc1 : Integrable (fun y ↦ ‖f y - c‖) (volume.restrict S) :=
    (hfc.integrable one_le_two).norm
  have hfa : MemLp (fun y ↦ f y - av) 2 (volume.restrict S) := hf.sub (memLp_const av)
  have hfa2 : Integrable (fun y ↦ ‖f y - av‖ ^ 2) (volume.restrict S) := hfa.norm.integrable_sq
  -- `m ‖c - av‖ ≤ ∫_S ‖f - c‖`
  have hmc : m * ‖c - av‖ ≤ ∫ y in S, ‖f y - c‖ := by
    have h1 : (m • (c - av)) = ∫ y in S, (c - f y) := by
      rw [integral_sub (integrable_const c) hfi, setIntegral_const, hav, setAverage_eq,
        smul_sub, smul_smul, mul_inv_cancel₀ hm.ne', one_smul]
    have h2 : ‖m • (c - av)‖ = m * ‖c - av‖ := by
      rw [norm_smul, Real.norm_of_nonneg hm.le]
    rw [← h2, h1]
    calc ‖∫ y in S, (c - f y)‖ ≤ ∫ y in S, ‖c - f y‖ := norm_integral_le_integral_norm _
      _ = ∫ y in S, ‖f y - c‖ := by simp_rw [norm_sub_rev]
  have hJ := sq_integral_le_measureReal_mul_integral_sq hfc1
    (by simpa only [norm_pow, norm_norm] using hfc2)
  rw [Measure.real, Measure.restrict_apply_univ] at hJ
  change (∫ y in S, ‖f y - c‖) ^ 2 ≤ m * ∫ y in S, ‖f y - c‖ ^ 2 at hJ
  have hca : m * ‖c - av‖ ^ 2 ≤ ∫ y in S, ‖f y - c‖ ^ 2 := by
    have h1 : (m * ‖c - av‖) ^ 2 ≤ m * ∫ y in S, ‖f y - c‖ ^ 2 :=
      (pow_le_pow_left₀ (by positivity) hmc 2).trans hJ
    have h2 : m * (m * ‖c - av‖ ^ 2) ≤ m * ∫ y in S, ‖f y - c‖ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left h2 hm
  have hpt : ∀ y, ‖f y - av‖ ^ 2 ≤ 2 * ‖f y - c‖ ^ 2 + 2 * ‖c - av‖ ^ 2 := by
    intro y
    have h1 : ‖f y - av‖ ≤ ‖f y - c‖ + ‖c - av‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    nlinarith [norm_nonneg (f y - av), norm_nonneg (f y - c), norm_nonneg (c - av),
      sq_nonneg (‖f y - c‖ - ‖c - av‖)]
  have hint : ∫ y in S, ‖f y - av‖ ^ 2 ≤ ∫ y in S, (2 * ‖f y - c‖ ^ 2 + 2 * ‖c - av‖ ^ 2) :=
    integral_mono hfa2 ((hfc2.const_mul 2).add (integrable_const _)) hpt
  rw [integral_add (hfc2.const_mul 2) (integrable_const _), integral_const_mul,
    setIntegral_const, smul_eq_mul, ← hmdef] at hint
  calc ∫ y in S, ‖f y - av‖ ^ 2 ≤ 2 * (∫ y in S, ‖f y - c‖ ^ 2) + m * (2 * ‖c - av‖ ^ 2) := hint
    _ = 2 * (∫ y in S, ‖f y - c‖ ^ 2) + 2 * (m * ‖c - av‖ ^ 2) := by ring
    _ ≤ 2 * (∫ y in S, ‖f y - c‖ ^ 2) + 2 * (∫ y in S, ‖f y - c‖ ^ 2) := by gcongr
    _ = 4 * ∫ y in S, ‖f y - c‖ ^ 2 := by ring

/-! ### The Dirichlet problem `L_{A₀} g = div F`, `g = 0` on `∂B`, in the very weak sense -/

private theorem measurable_gradient_aux (f : Space d → ℝ) : Measurable (gradient f) :=
  (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

private theorem norm_gradient_le_aux {f : Space d → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (y : Space d) : ‖gradient f y‖ ≤ K := by
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ hf

private theorem lipschitzWith_const_mul_aux {φ : Space d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (t : ℝ) : LipschitzWith (‖t‖₊ * K) (fun y ↦ t * φ y) := by
  refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
  rw [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by rw [← Real.dist_eq]; exact hφ.dist_le_mul y z)
    (abs_nonneg t)

private theorem memLp_two_ball_of_continuous_aux {f : Space d → ℝ} (hf : Continuous f)
    (x : Space d) (r : ℝ) : MemLp f 2 (volume.restrict (ball x r)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hf.continuousOn
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  exact MemLp.of_bound hf.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun y hy ↦
      hC y (ball_subset_closedBall hy)))

theorem aLaplacian_eq_zero_of_notMem_tsupport (A : Space d →L[ℝ] Space d) {φ : Space d → ℝ}
    {y : Space d} (hy : y ∉ tsupport φ) : aLaplacian A φ y = 0 := by
  have h : fderiv ℝ φ =ᶠ[𝓝 y] fun _ ↦ 0 := by
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hy] with z hz
    exact fderiv_of_notMem_tsupport ℝ hz
  simp [aLaplacian, h.fderiv_eq]

theorem continuous_aLaplacian (A : Space d →L[ℝ] Space d) {φ : Space d → ℝ}
    (hφ : ContDiff ℝ 2 φ) : Continuous (aLaplacian A φ) := by
  unfold aLaplacian
  refine continuous_finsetSum _ fun i _ ↦ ?_
  have h2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  exact (h2.clm_apply continuous_const).clm_apply continuous_const

/-- The quadratic energy `∫_B ⟪A₀ ∇ψ, ∇ψ⟫ + 2 ⟪F, ∇ψ⟫`. -/
def dirichletEnergy (A₀ : Space d →L[ℝ] Space d) (F : Space d → Space d) (B : Set (Space d))
    (ψ : Space d → ℝ) : ℝ :=
  ∫ y in B, (inner ℝ (A₀ (gradient ψ y)) (gradient ψ y) + 2 * inner ℝ (F y) (gradient ψ y))

theorem integrableOn_inner_apply_gradient (A₀ : Space d →L[ℝ] Space d) {ψ φ : Space d → ℝ}
    {K L : NNReal} (hψ : LipschitzWith K ψ) (hφ : LipschitzWith L φ) {B : Set (Space d)}
    (hB : volume B ≠ ⊤) :
    IntegrableOn (fun y ↦ inner ℝ (A₀ (gradient ψ y)) (gradient φ y)) B := by
  refine Measure.integrableOn_of_bounded (M := ‖A₀‖ * K * L) hB
    ((A₀.continuous.measurable.comp (measurable_gradient_aux ψ)).inner
      (measurable_gradient_aux φ)).aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  calc ‖inner ℝ (A₀ (gradient ψ y)) (gradient φ y)‖ ≤ ‖A₀ (gradient ψ y)‖ * ‖gradient φ y‖ :=
        norm_inner_le_norm _ _
    _ ≤ (‖A₀‖ * K) * L := mul_le_mul ((A₀.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_gradient_le_aux hψ y) (norm_nonneg _)))
        (norm_gradient_le_aux hφ y) (norm_nonneg _) (by positivity)

theorem integrableOn_inner_gradient_of_memLp {F : Space d → Space d} {φ : Space d → ℝ}
    {L : NNReal} (hφ : LipschitzWith L φ) {B : Set (Space d)} (hB : volume B ≠ ⊤)
    (hF : MemLp F 2 (volume.restrict B)) :
    IntegrableOn (fun y ↦ inner ℝ (F y) (gradient φ y)) B := by
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hB
  have hF1 : Integrable F (volume.restrict B) := hF.integrable one_le_two
  refine (hF1.norm.mul_const (L : ℝ)).mono'
    (hF.aestronglyMeasurable.inner (measurable_gradient_aux φ).aestronglyMeasurable)
    (Eventually.of_forall fun y ↦ ?_)
  calc ‖inner ℝ (F y) (gradient φ y)‖ ≤ ‖F y‖ * ‖gradient φ y‖ := norm_inner_le_norm _ _
    _ ≤ ‖F y‖ * L := mul_le_mul_of_nonneg_left (norm_gradient_le_aux hφ y) (norm_nonneg _)

private theorem integrableOn_norm_gradient_sq_aux {ψ : Space d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) {B : Set (Space d)} (hB : volume B ≠ ⊤) :
    IntegrableOn (fun y ↦ ‖gradient ψ y‖ ^ 2) B :=
  Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) hB
    ((measurable_gradient_aux ψ).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_aux hψ y) 2)

/-- Coercivity of the energy: `J(ψ) ≥ (ν/2) ∫_B ‖∇ψ‖² - (2/ν) ∫_B ‖F‖²`. -/
theorem dirichletEnergy_lower {A₀ : Space d →L[ℝ] Space d} {ν : ℝ} (hν : 0 < ν)
    (hell : ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A₀ ξ) ξ) {F : Space d → Space d} {B : Set (Space d)}
    (hB : volume B ≠ ⊤) (hF : MemLp F 2 (volume.restrict B)) {ψ : Space d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) :
    ν / 2 * (∫ y in B, ‖gradient ψ y‖ ^ 2) - 2 / ν * (∫ y in B, ‖F y‖ ^ 2) ≤
      dirichletEnergy A₀ F B ψ := by
  have h1 := integrableOn_norm_gradient_sq_aux hψ hB
  have h2 : IntegrableOn (fun y ↦ ‖F y‖ ^ 2) B := hF.norm.integrable_sq
  have hE : IntegrableOn (fun y ↦ inner ℝ (A₀ (gradient ψ y)) (gradient ψ y) +
      2 * inner ℝ (F y) (gradient ψ y)) B :=
    (integrableOn_inner_apply_gradient A₀ hψ hψ hB).add
      ((integrableOn_inner_gradient_of_memLp hψ hB hF).const_mul 2)
  have hpt : ∀ y, ν / 2 * ‖gradient ψ y‖ ^ 2 - 2 / ν * ‖F y‖ ^ 2 ≤
      inner ℝ (A₀ (gradient ψ y)) (gradient ψ y) + 2 * inner ℝ (F y) (gradient ψ y) := by
    intro y
    have ha := hell (gradient ψ y)
    have hb : |inner ℝ (F y) (gradient ψ y)| ≤ ‖F y‖ * ‖gradient ψ y‖ :=
      abs_real_inner_le_norm _ _
    have hkey : ν / 2 * ‖gradient ψ y‖ ^ 2 + 2 / ν * ‖F y‖ ^ 2 - 2 * (‖F y‖ * ‖gradient ψ y‖) =
        ν / 2 * (‖gradient ψ y‖ - 2 / ν * ‖F y‖) ^ 2 := by
      field_simp
      ring
    have hc : 0 ≤ ν / 2 * (‖gradient ψ y‖ - 2 / ν * ‖F y‖) ^ 2 := by positivity
    have hd : -(‖F y‖ * ‖gradient ψ y‖) ≤ inner ℝ (F y) (gradient ψ y) := by
      have := neg_abs_le (inner ℝ (F y) (gradient ψ y))
      linarith
    nlinarith
  have h1' : IntegrableOn (fun y ↦ ν / 2 * ‖gradient ψ y‖ ^ 2) B := h1.const_mul _
  have h2' : IntegrableOn (fun y ↦ 2 / ν * ‖F y‖ ^ 2) B := h2.const_mul _
  have hint : ∫ y in B, (ν / 2 * ‖gradient ψ y‖ ^ 2 - 2 / ν * ‖F y‖ ^ 2) ≤
      ∫ y in B, (inner ℝ (A₀ (gradient ψ y)) (gradient ψ y) +
        2 * inner ℝ (F y) (gradient ψ y)) :=
    integral_mono (h1'.sub h2') hE hpt
  rw [integral_sub h1' h2', integral_const_mul, integral_const_mul] at hint
  exact hint

/-- Expansion of the energy along a line `ψ + t φ` (for symmetric `A₀`). -/
theorem dirichletEnergy_add_smul {A₀ : Space d →L[ℝ] Space d}
    (hsymm : ∀ u v, inner ℝ (A₀ u) v = inner ℝ u (A₀ v)) {F : Space d → Space d}
    {B : Set (Space d)} (hB : volume B ≠ ⊤) (hF : MemLp F 2 (volume.restrict B))
    {ψ φ : Space d → ℝ} {K L : NNReal} (hψ : LipschitzWith K ψ) (hφ : LipschitzWith L φ)
    (t : ℝ) :
    dirichletEnergy A₀ F B (fun y ↦ ψ y + t * φ y) = dirichletEnergy A₀ F B ψ +
      2 * t * (∫ y in B, inner ℝ (A₀ (gradient ψ y) + F y) (gradient φ y)) +
      t ^ 2 * ∫ y in B, inner ℝ (A₀ (gradient φ y)) (gradient φ y) := by
  have hgrad : ∀ᵐ y, gradient (fun y ↦ ψ y + t * φ y) y = gradient ψ y + t • gradient φ y := by
    filter_upwards [hψ.ae_differentiableAt (μ := volume), hφ.ae_differentiableAt (μ := volume)]
      with y hψy hφy
    have hd : HasFDerivAt (fun y ↦ ψ y + t * φ y) (fderiv ℝ ψ y + t • fderiv ℝ φ y) y :=
      hψy.hasFDerivAt.add (hφy.hasFDerivAt.const_mul t)
    rw [gradient, hd.fderiv, map_add, map_smul]
    rfl
  have hX : IntegrableOn (fun y ↦ inner ℝ (A₀ (gradient ψ y)) (gradient ψ y) +
      2 * inner ℝ (F y) (gradient ψ y)) B :=
    (integrableOn_inner_apply_gradient A₀ hψ hψ hB).add
      ((integrableOn_inner_gradient_of_memLp hψ hB hF).const_mul 2)
  have hY : IntegrableOn (fun y ↦ inner ℝ (A₀ (gradient ψ y) + F y) (gradient φ y)) B := by
    have he : (fun y ↦ inner ℝ (A₀ (gradient ψ y) + F y) (gradient φ y)) =
        fun y ↦ inner ℝ (A₀ (gradient ψ y)) (gradient φ y) + inner ℝ (F y) (gradient φ y) := by
      funext y
      exact inner_add_left _ _ _
    rw [he]
    exact (integrableOn_inner_apply_gradient A₀ hψ hφ hB).add
      (integrableOn_inner_gradient_of_memLp hφ hB hF)
  have hZ := integrableOn_inner_apply_gradient A₀ hφ hφ hB
  have hcongr : dirichletEnergy A₀ F B (fun y ↦ ψ y + t * φ y) =
      ∫ y in B, ((inner ℝ (A₀ (gradient ψ y)) (gradient ψ y) + 2 * inner ℝ (F y) (gradient ψ y)) +
        2 * t * inner ℝ (A₀ (gradient ψ y) + F y) (gradient φ y) +
        t ^ 2 * inner ℝ (A₀ (gradient φ y)) (gradient φ y)) := by
    unfold dirichletEnergy
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hgrad] with y hy
    rw [hy]
    have h1 : inner ℝ (A₀ (gradient φ y)) (gradient ψ y) =
        inner ℝ (A₀ (gradient ψ y)) (gradient φ y) := by
      rw [hsymm, real_inner_comm]
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real, h1]
    ring
  have hYt : IntegrableOn (fun y ↦ 2 * t * inner ℝ (A₀ (gradient ψ y) + F y) (gradient φ y)) B :=
    hY.const_mul _
  have hXY : IntegrableOn (fun y ↦ (inner ℝ (A₀ (gradient ψ y)) (gradient ψ y) +
      2 * inner ℝ (F y) (gradient ψ y)) +
      2 * t * inner ℝ (A₀ (gradient ψ y) + F y) (gradient φ y)) B := hX.add hYt
  have hZt : IntegrableOn (fun y ↦ t ^ 2 * inner ℝ (A₀ (gradient φ y)) (gradient φ y)) B :=
    hZ.const_mul _
  rw [hcongr, integral_add hXY hZt, integral_add hX hYt, integral_const_mul, integral_const_mul]
  rfl

/-- If `2 t I + t² E ≥ -ε` for all `t` (with `E ≥ 0`), then `I² ≤ ε (E + 1)`. -/
theorem sq_le_of_forall_quadratic_ge {I E ε : ℝ} (hE : 0 ≤ E)
    (h : ∀ t : ℝ, -ε ≤ 2 * t * I + t ^ 2 * E) : I ^ 2 ≤ ε * (E + 1) := by
  have hs : 0 < E + 1 := by linarith
  have h1 := h (-I / (E + 1))
  have he : 2 * (-I / (E + 1)) * I + (-I / (E + 1)) ^ 2 * E =
      -(I ^ 2 * (E + 2)) / (E + 1) ^ 2 := by
    field_simp
    ring
  rw [he, le_div_iff₀ (by positivity)] at h1
  have h2 : I ^ 2 * (E + 1) ≤ I ^ 2 * (E + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg I)
  have h3 : I ^ 2 * (E + 1) ≤ ε * (E + 1) * (E + 1) := by nlinarith
  exact le_of_mul_le_mul_right (by linarith) hs

/-- **The Dirichlet problem for `L_{A₀}` with zero boundary values, very weak form.** For a
symmetric uniformly elliptic `A₀` and `F ∈ L²(B_r)` there is `g ∈ L²(B_r)` with
`∫_{B_r} g² ≤ 8 C_F r² ν⁻² ∫_{B_r} ‖F‖²` and `∫ g L_{A₀} φ = ∫ ⟪F, ∇φ⟫` for all smooth `φ`
compactly supported in `B_r`. It is the `L²` limit of a minimizing sequence of the energy
`∫ ⟪A₀ ∇ψ, ∇ψ⟫ + 2 ⟪F, ∇ψ⟫` over Lipschitz `ψ` supported in `B_r`. -/
theorem exists_veryWeak_dirichlet (hd : 0 < d) {A₀ : Space d →L[ℝ] Space d} {ν : ℝ}
    (hν : 0 < ν) (hsymm : ∀ u v, inner ℝ (A₀ u) v = inner ℝ u (A₀ v))
    (hell : ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A₀ ξ) ξ) {x : Space d} {r : ℝ} (hr : 0 < r)
    {F : Space d → Space d} (hF : MemLp F 2 (volume.restrict (ball x r))) :
    ∃ g : Space d → ℝ, MemLp g 2 (volume.restrict (ball x r)) ∧
      ∫ y in ball x r, g y ^ 2 ≤
        8 * friedrichsConst d / ν ^ 2 * r ^ 2 * ∫ y in ball x r, ‖F y‖ ^ 2 ∧
      ∀ φ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ ball x r →
          ∫ y, g y * aLaplacian A₀ φ y = ∫ y, inner ℝ (F y) (gradient φ y) := by
  have hB : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  set f2 := ∫ y in ball x r, ‖F y‖ ^ 2 with hf2
  have hf20 : 0 ≤ f2 := integral_nonneg fun _ ↦ sq_nonneg _
  set Adm : Set (Space d → ℝ) :=
    {ψ | (∃ K, LipschitzWith K ψ) ∧ tsupport ψ ⊆ ball x r} with hAdm
  set J : (Space d → ℝ) → ℝ := dirichletEnergy A₀ F (ball x r) with hJ
  have hlow : ∀ ψ ∈ Adm, ν / 2 * (∫ y in ball x r, ‖gradient ψ y‖ ^ 2) - 2 / ν * f2 ≤ J ψ := by
    rintro ψ ⟨⟨K, hK⟩, -⟩
    exact dirichletEnergy_lower hν hell hB hF hK
  have h0 : (fun _ ↦ (0 : ℝ)) ∈ Adm := ⟨⟨0, LipschitzWith.const 0⟩, by simp⟩
  have hJ0 : J (fun _ ↦ (0 : ℝ)) = 0 := by
    simp [hJ, dirichletEnergy, gradient]
  have hbdd : BddBelow (J '' Adm) := by
    refine ⟨-(2 / ν * f2), ?_⟩
    rintro _ ⟨ψ, hψ, rfl⟩
    have h1 := hlow ψ hψ
    have h2 : 0 ≤ ν / 2 * (∫ y in ball x r, ‖gradient ψ y‖ ^ 2) :=
      mul_nonneg (by positivity) (integral_nonneg fun _ ↦ sq_nonneg _)
    linarith
  have hne : (J '' Adm).Nonempty := ⟨_, ⟨_, h0, rfl⟩⟩
  set m := sInf (J '' Adm) with hm
  have hm0 : m ≤ 0 := by
    have := csInf_le hbdd ⟨_, h0, rfl⟩
    rwa [hJ0] at this
  have hmJ : ∀ ψ ∈ Adm, m ≤ J ψ := fun ψ hψ ↦ csInf_le hbdd ⟨ψ, hψ, rfl⟩
  have hseq : ∀ k : ℕ, ∃ ψ ∈ Adm, J ψ < m + 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨_, ⟨ψ, hψ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne
      (lt_add_of_pos_right m (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
    exact ⟨ψ, hψ, hlt⟩
  choose ψ hψAdm hψJ using hseq
  choose K hK using fun k ↦ (hψAdm k).1
  have hψsupp : ∀ k, tsupport (ψ k) ⊆ ball x r := fun k ↦ (hψAdm k).2
  have hε0 : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k ↦ by positivity
  have hε1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k ↦ by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  -- energy bounds for the minimizing sequence
  have hgrad : ∀ k, ∫ y in ball x r, ‖gradient (ψ k) y‖ ^ 2 ≤
      2 / ν * (1 / ((k : ℝ) + 1) + 2 / ν * f2) := by
    intro k
    have h1 := hlow (ψ k) (hψAdm k)
    have h2 := hψJ k
    have h3 : ν / 2 * (∫ y in ball x r, ‖gradient (ψ k) y‖ ^ 2) ≤
        1 / ((k : ℝ) + 1) + 2 / ν * f2 := by linarith
    calc ∫ y in ball x r, ‖gradient (ψ k) y‖ ^ 2 =
          2 / ν * (ν / 2 * ∫ y in ball x r, ‖gradient (ψ k) y‖ ^ 2) := by
          field_simp
      _ ≤ 2 / ν * (1 / ((k : ℝ) + 1) + 2 / ν * f2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hgrad' : ∀ k, ∫ y in ball x r, ‖fderiv ℝ (ψ k) y‖ ^ 2 ≤
      2 / ν * (1 / ((k : ℝ) + 1) + 2 / ν * f2) := fun k ↦ by
    simpa only [norm_gradient_eq_norm_fderiv] using hgrad k
  have hsq : ∀ k, ∫ y in ball x r, ψ k y ^ 2 ≤
      friedrichsConst d * r ^ 2 * (2 / ν * (1 / ((k : ℝ) + 1) + 2 / ν * f2)) := fun k ↦
    (friedrichs_ball hd x hr (hK k) (hψsupp k)).trans
      (mul_le_mul_of_nonneg_left (hgrad' k) (by have := friedrichsConst_nonneg d; positivity))
  -- Rellich compactness on the doubled ball
  set M := (friedrichsConst d * r ^ 2 + 1) * (2 / ν * (1 + 2 / ν * f2)) with hMdef
  have hM : ∀ k, ∫ y in ball x (2 * r), (ψ k y ^ 2 + ‖fderiv ℝ (ψ k) y‖ ^ 2) ≤ M := by
    intro k
    have hzero : ∀ y ∈ ball x (2 * r) \ ball x r, ψ k y ^ 2 + ‖fderiv ℝ (ψ k) y‖ ^ 2 = 0 := by
      intro y hy
      have hy' : y ∉ tsupport (ψ k) := fun h ↦ hy.2 (hψsupp k h)
      rw [image_eq_zero_of_notMem_tsupport hy', fderiv_of_notMem_tsupport ℝ hy']
      simp
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball
      (ball_subset_ball (by linarith)) hzero]
    have hi1 : IntegrableOn (fun y ↦ ψ k y ^ 2) (ball x r) :=
      ((((hK k).continuous.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall x r))).mono_set ball_subset_closedBall
    have hi2 : IntegrableOn (fun y ↦ ‖fderiv ℝ (ψ k) y‖ ^ 2) (ball x r) := by
      simpa only [norm_gradient_eq_norm_fderiv] using integrableOn_norm_gradient_sq_aux (hK k) hB
    rw [integral_add hi1 hi2]
    have hD0 : 0 ≤ 2 / ν * (1 / ((k : ℝ) + 1) + 2 / ν * f2) := by
      have := hε0 k
      positivity
    have hDle : 2 / ν * (1 / ((k : ℝ) + 1) + 2 / ν * f2) ≤ 2 / ν * (1 + 2 / ν * f2) :=
      mul_le_mul_of_nonneg_left (by linarith [hε1 k]) (by positivity)
    have hC0 : 0 ≤ friedrichsConst d * r ^ 2 := by
      have := friedrichsConst_nonneg d
      positivity
    calc (∫ y in ball x r, ψ k y ^ 2) + ∫ y in ball x r, ‖fderiv ℝ (ψ k) y‖ ^ 2 ≤
        friedrichsConst d * r ^ 2 * (2 / ν * (1 / ((k : ℝ) + 1) + 2 / ν * f2)) +
          2 / ν * (1 / ((k : ℝ) + 1) + 2 / ν * f2) := add_le_add (hsq k) (hgrad' k)
      _ = (friedrichsConst d * r ^ 2 + 1) * (2 / ν * (1 / ((k : ℝ) + 1) + 2 / ν * f2)) := by
          ring
      _ ≤ M := mul_le_mul_of_nonneg_left hDle (by linarith)
  obtain ⟨σ, hσ, g, -, hgL2, hconv⟩ :=
    exists_subseq_tendsto_sq_integral_ball x (2 * r) M ψ (fun k ↦ ⟨K k, hK k⟩) hM
  have hgB : MemLp g 2 (volume.restrict (ball x r)) := hgL2 r (by linarith)
  have hconvB := hconv r (by linarith)
  -- the variational inequality
  have hvar : ∀ k, ∀ φ ∈ Adm,
      (∫ y in ball x r, inner ℝ (A₀ (gradient (ψ k) y) + F y) (gradient φ y)) ^ 2 ≤
        1 / ((k : ℝ) + 1) * ((∫ y in ball x r, inner ℝ (A₀ (gradient φ y)) (gradient φ y)) + 1) := by
    rintro k φ ⟨⟨L, hL⟩, hφB⟩
    apply sq_le_of_forall_quadratic_ge
    · exact setIntegral_nonneg measurableSet_ball fun y _ ↦
        (mul_nonneg hν.le (sq_nonneg _)).trans (hell _)
    · intro t
      have hadm : (fun y ↦ ψ k y + t * φ y) ∈ Adm := by
        refine ⟨⟨_, (hK k).add (lipschitzWith_const_mul_aux hL t)⟩, ?_⟩
        exact (tsupport_add _ _).trans (union_subset (hψsupp k)
          (tsupport_mul_subset_right.trans hφB))
      have h1 := hmJ _ hadm
      have h2 := hψJ k
      have h3 := dirichletEnergy_add_smul hsymm hB hF (hK k) hL t
      simp only [hJ] at h1 h2
      rw [h3] at h1
      linarith
  refine ⟨g, hgB, ?_, ?_⟩
  · -- the `L²` bound passes to the limit
    have hbound : ∀ j, ∫ y in ball x r, g y ^ 2 ≤
        2 * (∫ y in ball x r, (ψ (σ j) y - g y) ^ 2) +
          2 * (friedrichsConst d * r ^ 2 * (2 / ν * (1 / ((σ j : ℝ) + 1) + 2 / ν * f2))) := by
      intro j
      have hψL2 := memLp_two_ball_of_continuous_aux (hK (σ j)).continuous x r
      have hi1 : IntegrableOn (fun y ↦ (ψ (σ j) y - g y) ^ 2) (ball x r) :=
        (hψL2.sub hgB).integrable_sq
      have hi2 : IntegrableOn (fun y ↦ ψ (σ j) y ^ 2) (ball x r) := hψL2.integrable_sq
      have hi1' : IntegrableOn (fun y ↦ 2 * (ψ (σ j) y - g y) ^ 2) (ball x r) := hi1.const_mul 2
      have hi2' : IntegrableOn (fun y ↦ 2 * ψ (σ j) y ^ 2) (ball x r) := hi2.const_mul 2
      have h1 : ∫ y in ball x r, g y ^ 2 ≤
          ∫ y in ball x r, (2 * (ψ (σ j) y - g y) ^ 2 + 2 * ψ (σ j) y ^ 2) :=
        integral_mono hgB.integrable_sq (hi1'.add hi2') (fun y ↦ by
          nlinarith [sq_nonneg (2 * ψ (σ j) y - g y)])
      rw [integral_add hi1' hi2', integral_const_mul, integral_const_mul] at h1
      have h2 := hsq (σ j)
      linarith
    have hlimε : Tendsto (fun j ↦ 1 / ((σ j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hσ.tendsto_atTop
    have hlim : Tendsto (fun j ↦ 2 * (∫ y in ball x r, (ψ (σ j) y - g y) ^ 2) +
        2 * (friedrichsConst d * r ^ 2 * (2 / ν * (1 / ((σ j : ℝ) + 1) + 2 / ν * f2))))
        atTop (𝓝 (2 * 0 + 2 * (friedrichsConst d * r ^ 2 * (2 / ν * (0 + 2 / ν * f2))))) :=
      (hconvB.const_mul 2).add
        (((hlimε.add_const _).const_mul _ |>.const_mul _).const_mul _)
    have h := ge_of_tendsto' hlim hbound
    calc ∫ y in ball x r, g y ^ 2 ≤
        2 * 0 + 2 * (friedrichsConst d * r ^ 2 * (2 / ν * (0 + 2 / ν * f2))) := h
      _ = 8 * friedrichsConst d / ν ^ 2 * r ^ 2 * f2 := by
          field_simp
          ring
  · intro φ hφ hφc hφB
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
    have hφAdm : φ ∈ Adm := ⟨⟨L, hL⟩, hφB⟩
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
    set χ := aLaplacian A₀ φ with hχ
    have hχc : Continuous χ := continuous_aLaplacian A₀ hφ2
    have hχ0 : ∀ y, y ∉ tsupport φ → χ y = 0 := fun y hy ↦
      aLaplacian_eq_zero_of_notMem_tsupport A₀ hy
    have hχcs : HasCompactSupport χ := by
      refine hφc.mono' (fun y hy ↦ ?_)
      by_contra hn
      exact hy (hχ0 y hn)
    obtain ⟨Cχ, hCχ⟩ := hχcs.exists_bound_of_continuous hχc
    have hgφ0 : ∀ y, y ∉ ball x r → gradient φ y = 0 := fun y hy ↦
      gradient_eq_zero_of_notMem_tsupport (fun h ↦ hy (hφB h))
    -- integration by parts for the sequence
    have hIBP : ∀ k, ∫ y, ψ k y * χ y =
        -∫ y, inner ℝ (A₀ (gradient (ψ k) y)) (gradient φ y) := fun k ↦
      integral_mul_aLaplacian_eq_neg_of_lipschitz A₀ (hK k) hφ2 hφc
    have hsplit : ∀ k, ∫ y, inner ℝ (A₀ (gradient (ψ k) y)) (gradient φ y) =
        (∫ y in ball x r, inner ℝ (A₀ (gradient (ψ k) y) + F y) (gradient φ y)) -
          ∫ y, inner ℝ (F y) (gradient φ y) := by
      intro k
      have e1 : ∫ y, inner ℝ (A₀ (gradient (ψ k) y)) (gradient φ y) =
          ∫ y in ball x r, inner ℝ (A₀ (gradient (ψ k) y)) (gradient φ y) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by simp [hgφ0 y hy])).symm
      have e2 : ∫ y, inner ℝ (F y) (gradient φ y) = ∫ y in ball x r, inner ℝ (F y) (gradient φ y) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by simp [hgφ0 y hy])).symm
      rw [e1, e2]
      have he : (fun y ↦ inner ℝ (A₀ (gradient (ψ k) y) + F y) (gradient φ y)) =
          fun y ↦ inner ℝ (A₀ (gradient (ψ k) y)) (gradient φ y) +
            inner ℝ (F y) (gradient φ y) := by
        funext y
        exact inner_add_left _ _ _
      rw [he, integral_add (integrableOn_inner_apply_gradient A₀ (hK k) hL hB)
        (integrableOn_inner_gradient_of_memLp hL hB hF)]
      ring
    -- the first variations tend to zero
    set E := ∫ y in ball x r, inner ℝ (A₀ (gradient φ y)) (gradient φ y) with hE
    have hI : Tendsto (fun k ↦ ∫ y in ball x r,
        inner ℝ (A₀ (gradient (ψ k) y) + F y) (gradient φ y)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) * (E + 1)) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (E + 1)
      have h2 : Tendsto (fun k ↦ (∫ y in ball x r,
          inner ℝ (A₀ (gradient (ψ k) y) + F y) (gradient φ y)) ^ 2) atTop (𝓝 0) :=
        squeeze_zero (fun k ↦ sq_nonneg _) (fun k ↦ hvar k φ hφAdm) h1
      have h3 := h2.sqrt
      simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h3
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [Real.norm_eq_abs] using h3
    -- passing to the limit
    have hgi : Integrable (fun y ↦ g y * χ y) := by
      have : IsFiniteMeasure (volume.restrict (ball x r)) := isFiniteMeasure_restrict.2 hB
      have h1 : IntegrableOn (fun y ↦ χ y * g y) (ball x r) :=
        (hgB.integrable one_le_two).bdd_mul hχc.aestronglyMeasurable
          (Eventually.of_forall fun y ↦ hCχ y)
      refine (h1.congr_fun (fun y _ ↦ mul_comm _ _) measurableSet_ball).integrable_of_forall_notMem_eq_zero
        (fun y hy ↦ ?_)
      rw [hχ0 y (fun h ↦ hy (hφB h)), mul_zero]
    have hlim1 : Tendsto (fun j ↦ ∫ y, ψ (σ j) y * χ y) atTop (𝓝 (∫ y, g y * χ y)) := by
      refine tendsto_integral_mul_of_sq_tendsto hB
        (fun j ↦ (memLp_two_ball_of_continuous_aux (hK (σ j)).continuous x r).sub hgB) hconvB
        (B := Cχ) (fun y ↦ by rw [← Real.norm_eq_abs]; exact hCχ y)
        (fun y hy ↦ hχ0 y (fun h ↦ hy (hφB h)))
        (fun j ↦ ((hK (σ j)).continuous.mul hχc).integrable_of_hasCompactSupport
          hχcs.mul_left) hgi
    have hlim2 : Tendsto (fun j ↦ ∫ y, ψ (σ j) y * χ y) atTop
        (𝓝 (∫ y, inner ℝ (F y) (gradient φ y))) := by
      have he : ∀ j, ∫ y, ψ (σ j) y * χ y = (∫ y, inner ℝ (F y) (gradient φ y)) -
          ∫ y in ball x r, inner ℝ (A₀ (gradient (ψ (σ j)) y) + F y) (gradient φ y) := by
        intro j
        rw [hIBP, hsplit]
        ring
      simp_rw [he]
      simpa using (tendsto_const_nhds (x := ∫ y, inner ℝ (F y) (gradient φ y))).sub
        (hI.comp hσ.tendsto_atTop)
    exact tendsto_nhds_unique hlim1 hlim2

/-! ### Comparison with `A₀`-harmonic functions -/

private theorem measurable_gradient_aux' (f : Space d → ℝ) : Measurable (gradient f) :=
  (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

private theorem norm_gradient_le_aux' {f : Space d → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (y : Space d) : ‖gradient f y‖ ≤ K := by
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ hf

/-- A vector field continuous on a set, paired with the gradient of a Lipschitz test compactly
supported in the set, is integrable. -/
theorem integrable_inner_gradient_of_continuousOn {U : Set (Space d)} {V : Space d → Space d}
    (hV : ContinuousOn V U) {ψ : Space d → ℝ} {K : NNReal} (hψ : LipschitzWith K ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
    Integrable (fun y ↦ inner ℝ (V y) (gradient ψ y)) := by
  obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn (hV.mono hψU)
  have : IsFiniteMeasure (volume.restrict (tsupport ψ)) :=
    isFiniteMeasure_restrict.2 hc.isCompact.measure_lt_top.ne
  have hm : AEStronglyMeasurable (fun y ↦ inner ℝ (V y) (gradient ψ y))
      (volume.restrict (tsupport ψ)) :=
    ((hV.mono hψU).aestronglyMeasurable (isClosed_tsupport ψ).measurableSet).inner
      (measurable_gradient_aux' ψ).aestronglyMeasurable
  have hi : IntegrableOn (fun y ↦ inner ℝ (V y) (gradient ψ y)) (tsupport ψ) := by
    refine (integrable_const (C * K)).mono' hm ?_
    filter_upwards [ae_restrict_mem (isClosed_tsupport ψ).measurableSet] with y hy
    calc ‖inner ℝ (V y) (gradient ψ y)‖ ≤ ‖V y‖ * ‖gradient ψ y‖ := norm_inner_le_norm _ _
      _ ≤ C * K := mul_le_mul (hC y hy) (norm_gradient_le_aux' hψ y) (norm_nonneg _)
          ((norm_nonneg _).trans (hC y hy))
  exact hi.integrable_of_forall_notMem_eq_zero (fun y hy ↦ by
    rw [gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right])

/-- An `L²(B)` vector field paired with the gradient of a Lipschitz test supported in `B` is
integrable. -/
theorem integrable_inner_gradient_of_memLp {x : Space d} {r : ℝ} {F : Space d → Space d}
    (hF : MemLp F 2 (volume.restrict (ball x r))) {ψ : Space d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) (hψB : tsupport ψ ⊆ ball x r) :
    Integrable (fun y ↦ inner ℝ (F y) (gradient ψ y)) :=
  (integrableOn_inner_gradient_of_memLp hψ measure_ball_lt_top.ne hF).integrable_of_forall_notMem_eq_zero
    (fun y hy ↦ by
      rw [gradient_eq_zero_of_notMem_tsupport (fun h ↦ hy (hψB h)), inner_zero_right])

/-- The constant of the comparison estimate. -/
def comparisonConst (d : ℕ) (ν Λ : ℝ) : ℝ :=
  2 / ν * ((4 * Λ ^ 2 / ν + 1) * (512 * friedrichsConst d / ν ^ 2) + (1 / ν + 1))

theorem comparisonConst_nonneg (d : ℕ) {ν : ℝ} (hν : 0 < ν) (Λ : ℝ) :
    0 ≤ comparisonConst d ν Λ := by
  unfold comparisonConst
  have := friedrichsConst_nonneg d
  positivity

/-- **Comparison with an `A₀`-harmonic function.** If a Lipschitz `u` solves
`div (A₀ ∇u) = div F` weakly in `B_r`, then there is a smooth `A₀`-harmonic `v` on `B_r` with
`∫_{B_{r/2}} ‖Du - Dv‖² ≤ C ∫_{B_r} ‖F‖²`, `C = comparisonConst d ν Λ`. -/
theorem exists_aHarmonic_comparison (hd : 0 < d) {A₀ : Space d →L[ℝ] Space d} {ν Λ : ℝ}
    (hν : 0 < ν) (hsymm : ∀ u v, inner ℝ (A₀ u) v = inner ℝ u (A₀ v))
    (hell : ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A₀ ξ) ξ) (hbd : ‖A₀‖ ≤ Λ)
    {x : Space d} {r : ℝ} (hr : 0 < r)
    {F : Space d → Space d} (hF : MemLp F 2 (volume.restrict (ball x r)))
    {u : Space d → ℝ} {K : NNReal} (hu : LipschitzWith K u)
    (heq : IsWeakDivFree (fun y ↦ A₀ (gradient u y) - F y) (ball x r)) :
    ∃ v : Space d → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v (ball x r) ∧
      (∀ y ∈ ball x r, aLaplacian A₀ v y = 0) ∧
      ∫ y in ball x (r / 2), ‖fderiv ℝ u y - fderiv ℝ v y‖ ^ 2 ≤
        comparisonConst d ν Λ * ∫ y in ball x r, ‖F y‖ ^ 2 := by
  obtain ⟨g, hgL2, hgbd, hgeq⟩ := exists_veryWeak_dirichlet hd hν hsymm hell hr hF
  have hB : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball x r)) := isFiniteMeasure_restrict.2 hB
  set f2 := ∫ y in ball x r, ‖F y‖ ^ 2 with hf2
  have hf20 : 0 ≤ f2 := integral_nonneg fun _ ↦ sq_nonneg _
  -- integrability of `g L φ`
  have hgχ : ∀ φ : Space d → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ ball x r →
      Integrable (fun y ↦ g y * aLaplacian A₀ φ y) := by
    intro φ hφ hφc hφB
    have hχc : Continuous (aLaplacian A₀ φ) := continuous_aLaplacian A₀ hφ
    have hχcs : HasCompactSupport (aLaplacian A₀ φ) := by
      refine hφc.mono' (fun y hy ↦ ?_)
      by_contra hn
      exact hy (aLaplacian_eq_zero_of_notMem_tsupport A₀ hn)
    obtain ⟨Cχ, hCχ⟩ := hχcs.exists_bound_of_continuous hχc
    have h1 : IntegrableOn (fun y ↦ aLaplacian A₀ φ y * g y) (ball x r) :=
      (hgL2.integrable one_le_two).bdd_mul hχc.aestronglyMeasurable
        (Eventually.of_forall fun y ↦ hCχ y)
    refine (h1.congr_fun (fun y _ ↦ mul_comm _ _) measurableSet_ball).integrable_of_forall_notMem_eq_zero
      (fun y hy ↦ ?_)
    rw [aLaplacian_eq_zero_of_notMem_tsupport A₀ (fun h ↦ hy (hφB h)), mul_zero]
  -- `u + g` is very weakly `A₀`-harmonic
  have hvh : IsVeryWeaklyAHarmonicOn A₀ (ball x r) (fun y ↦ u y + g y) := by
    refine ⟨(hu.continuous.locallyIntegrable.locallyIntegrableOn _).add
      (IntegrableOn.locallyIntegrableOn (hgL2.integrable one_le_two)), ?_⟩
    intro φ hφ hφc hφB
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
    have h1 := integral_mul_aLaplacian_eq_neg_of_lipschitz A₀ hu hφ2 hφc
    have h2 := hgeq φ hφ hφc hφB
    have h3 := heq φ ⟨L, hL⟩ hφc hφB
    have hiu : Integrable (fun y ↦ u y * aLaplacian A₀ φ y) := by
      have hχcs : HasCompactSupport (aLaplacian A₀ φ) := by
        refine hφc.mono' (fun y hy ↦ ?_)
        by_contra hn
        exact hy (aLaplacian_eq_zero_of_notMem_tsupport A₀ hn)
      exact (hu.continuous.mul (continuous_aLaplacian A₀ hφ2)).integrable_of_hasCompactSupport
        hχcs.mul_left
    have hsplit : (fun y ↦ (u y + g y) * aLaplacian A₀ φ y) =
        fun y ↦ u y * aLaplacian A₀ φ y + g y * aLaplacian A₀ φ y := by
      funext y
      ring
    rw [hsplit, integral_add hiu (hgχ φ hφ2 hφc hφB), h1, h2]
    have hA : Integrable (fun y ↦ inner ℝ (A₀ (gradient u y)) (gradient φ y)) :=
      (integrableOn_inner_apply_gradient A₀ hu hL hB).integrable_of_forall_notMem_eq_zero
        (fun y hy ↦ by
          rw [gradient_eq_zero_of_notMem_tsupport (fun h ↦ hy (hφB h)), inner_zero_right])
    have hFi := integrable_inner_gradient_of_memLp hF hL hφB
    have h4 : ∫ y, inner ℝ (A₀ (gradient u y) - F y) (gradient φ y) =
        (∫ y, inner ℝ (A₀ (gradient u y)) (gradient φ y)) - ∫ y, inner ℝ (F y) (gradient φ y) := by
      rw [← integral_sub hA hFi]
      congr 1
      funext y
      exact inner_sub_left _ _ _
    rw [h4] at h3
    linarith
  obtain ⟨v, hv, hLv, hae⟩ := aWeyl_lemma hsymm hν hell isOpen_ball hvh
  refine ⟨v, hv, hLv, ?_⟩
  have hv1 : ContDiffOn ℝ 1 v (ball x r) := hv.of_le (by simp)
  -- `∫_B (u - v)² = ∫_B g²`
  have hsq_ae : ∀ᵐ y ∂(volume.restrict (ball x r)), (u y - v y) ^ 2 = g y ^ 2 := by
    filter_upwards [hae] with y hy
    have hy' : u y + g y = v y := hy
    have : u y - v y = -g y := by linarith
    rw [this, neg_sq]
  have hsq_int : IntegrableOn (fun y ↦ (u y - v y) ^ 2) (ball x r) :=
    hgL2.integrable_sq.congr (hsq_ae.mono fun y hy ↦ hy.symm)
  have hsq_eq : ∫ y in ball x r, (u y - v y) ^ 2 = ∫ y in ball x r, g y ^ 2 :=
    integral_congr_ae hsq_ae
  -- `v` is weakly `A₀`-harmonic against Lipschitz tests
  have hgradv_cont : ContinuousOn (fun y ↦ A₀ (gradient v y)) (ball x r) := by
    have h1 : ContinuousOn (fderiv ℝ v) (ball x r) :=
      hv1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
    exact A₀.continuous.comp_continuousOn
      ((toDual ℝ (Space d)).symm.continuous.comp_continuousOn h1)
  have hvweak : IsWeakDivFree (fun y ↦ A₀ (gradient v y)) (ball x r) := by
    refine IsWeakDivFree.of_smooth isOpen_ball
      (hgradv_cont.locallyIntegrableOn measurableSet_ball) ?_
    intro φ hφ hφc hφB
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
    have h1 := integral_mul_aLaplacian_eq_neg_of_contDiffOn A₀ isOpen_ball hv1 hφ2 hφc hφB
    have hz1 : ∀ y, y ∉ ball x r → v y * aLaplacian A₀ φ y = 0 := fun y hy ↦ by
      rw [aLaplacian_eq_zero_of_notMem_tsupport A₀ (fun h ↦ hy (hφB h)), mul_zero]
    have hz2 : ∀ y, y ∉ ball x r → (u y + g y) * aLaplacian A₀ φ y = 0 := fun y hy ↦ by
      rw [aLaplacian_eq_zero_of_notMem_tsupport A₀ (fun h ↦ hy (hφB h)), mul_zero]
    have e1 : ∫ y, v y * aLaplacian A₀ φ y = ∫ y in ball x r, v y * aLaplacian A₀ φ y :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hz1).symm
    have e2 : ∫ y, (u y + g y) * aLaplacian A₀ φ y =
        ∫ y in ball x r, (u y + g y) * aLaplacian A₀ φ y :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hz2).symm
    have h2 : ∫ y in ball x r, v y * aLaplacian A₀ φ y =
        ∫ y in ball x r, (u y + g y) * aLaplacian A₀ φ y := by
      apply integral_congr_ae
      filter_upwards [hae] with y hy
      have hy' : u y + g y = v y := hy
      rw [hy']
    have h3 := hvh.2 φ hφ hφc hφB
    rw [e1, h2, ← e2, h3] at h1
    linarith
  -- the Lipschitz extension of `u - v` from `closedBall x (3r/4)`
  have hsub34 : closedBall x (3 * r / 4) ⊆ ball x r := closedBall_subset_ball (by linarith)
  obtain ⟨Lv, hLvl⟩ := (hv1.mono hsub34).exists_lipschitzOnWith (by simp)
    (convex_closedBall x _) (isCompact_closedBall x _)
  obtain ⟨z, hz, hzeq⟩ := ((hu.lipschitzOnWith (s := closedBall x (3 * r / 4))).sub hLvl).extend_real
  have hgz : ∀ᵐ y, y ∈ ball x (3 * r / 4) → gradient z y = gradient u y - gradient v y := by
    filter_upwards [hu.ae_differentiableAt (μ := volume)] with y huy hy
    have hev : z =ᶠ[𝓝 y] fun w ↦ u w - v w := by
      filter_upwards [isOpen_ball.mem_nhds hy] with w hw
      exact (hzeq (ball_subset_closedBall hw)).symm
    have hyB : y ∈ ball x r := hsub34 (ball_subset_closedBall hy)
    have hvy : DifferentiableAt ℝ v y :=
      (hv1.differentiableOn one_ne_zero y hyB).differentiableAt (isOpen_ball.mem_nhds hyB)
    rw [gradient, gradient, gradient, hev.fderiv_eq, fderiv_fun_sub huy hvy, map_sub]
  have hzdiv : IsWeakDivFree (fun y ↦ A₀ (gradient z y) - F y) (ball x (3 * r / 4)) := by
    rintro ψ ⟨Lψ, hψ⟩ hψc hψB
    have hψB' : tsupport ψ ⊆ ball x r := hψB.trans (ball_subset_ball (by linarith))
    have h1 := heq ψ ⟨Lψ, hψ⟩ hψc hψB'
    have h2 := hvweak ψ ⟨Lψ, hψ⟩ hψc hψB'
    have hiA : Integrable (fun y ↦ inner ℝ (A₀ (gradient u y)) (gradient ψ y)) :=
      (integrableOn_inner_apply_gradient A₀ hu hψ hB).integrable_of_forall_notMem_eq_zero
        (fun y hy ↦ by
          rw [gradient_eq_zero_of_notMem_tsupport (fun h ↦ hy (hψB' h)), inner_zero_right])
    have hiF := integrable_inner_gradient_of_memLp hF hψ hψB'
    have hi1 : Integrable (fun y ↦ inner ℝ (A₀ (gradient u y) - F y) (gradient ψ y)) := by
      have he : (fun y ↦ inner ℝ (A₀ (gradient u y) - F y) (gradient ψ y)) =
          fun y ↦ inner ℝ (A₀ (gradient u y)) (gradient ψ y) - inner ℝ (F y) (gradient ψ y) := by
        funext y
        exact inner_sub_left _ _ _
      rw [he]
      exact hiA.sub hiF
    have hi2 : Integrable (fun y ↦ inner ℝ (A₀ (gradient v y)) (gradient ψ y)) :=
      integrable_inner_gradient_of_continuousOn hgradv_cont hψ hψc hψB'
    have hcongr : ∫ y, inner ℝ (A₀ (gradient z y) - F y) (gradient ψ y) =
        ∫ y, (inner ℝ (A₀ (gradient u y) - F y) (gradient ψ y) -
          inner ℝ (A₀ (gradient v y)) (gradient ψ y)) := by
      apply integral_congr_ae
      filter_upwards [hgz] with y hy
      by_cases hyB : y ∈ ball x (3 * r / 4)
      · rw [hy hyB, map_sub, ← inner_sub_left]
        congr 1
        abel
      · rw [gradient_eq_zero_of_notMem_tsupport (fun h ↦ hyB (hψB h))]
        simp
    rw [hcongr, integral_sub hi1 hi2, h1, h2, sub_zero]
  -- Caccioppoli for `z`
  have hF34 : MemLp F 2 (volume.restrict (ball x (3 * r / 4))) :=
    hF.mono_measure (Measure.restrict_mono (ball_subset_ball (by linarith)) le_rfl)
  have hcac := caccioppoli (a := fun _ ↦ A₀) (Λ := Λ) hν (x₀ := x) (ρ := r / 2)
    (s := 3 * r / 4) (by linarith) aestronglyMeasurable_const (fun _ _ ξ ↦ hell ξ)
    (fun _ _ ↦ hbd) hF34 hz hzdiv
  have hz2 : ∫ y in ball x (3 * r / 4), z y ^ 2 ≤
      8 * friedrichsConst d / ν ^ 2 * r ^ 2 * f2 := by
    have e1 : ∫ y in ball x (3 * r / 4), z y ^ 2 = ∫ y in ball x (3 * r / 4), (u y - v y) ^ 2 :=
      setIntegral_congr_fun measurableSet_ball (fun y hy ↦ by
        rw [← hzeq (ball_subset_closedBall hy)])
    rw [e1]
    calc ∫ y in ball x (3 * r / 4), (u y - v y) ^ 2 ≤ ∫ y in ball x r, (u y - v y) ^ 2 :=
          setIntegral_mono_set hsq_int (Eventually.of_forall fun y ↦ sq_nonneg _)
            (ball_subset_ball (by linarith)).eventuallyLE
      _ = ∫ y in ball x r, g y ^ 2 := hsq_eq
      _ ≤ 8 * friedrichsConst d / ν ^ 2 * r ^ 2 * f2 := hgbd
  have hF2 : ∫ y in ball x (3 * r / 4), ‖F y‖ ^ 2 ≤ f2 :=
    setIntegral_mono_set hF.norm.integrable_sq (Eventually.of_forall fun y ↦ sq_nonneg _)
      (ball_subset_ball (by linarith)).eventuallyLE
  have hlhs : ∫ y in ball x (r / 2), ‖fderiv ℝ u y - fderiv ℝ v y‖ ^ 2 =
      ∫ y in ball x (r / 2), ‖gradient z y‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hgz, ae_restrict_mem measurableSet_ball] with y hy hyB
    rw [hy (ball_subset_ball (by linarith) hyB), gradient, gradient, ← map_sub,
      LinearIsometryEquiv.norm_map]
  rw [hlhs]
  have hr2 : (2 / (3 * r / 4 - r / 2)) ^ 2 = 64 / r ^ 2 := by
    field_simp
    ring
  rw [hr2] at hcac
  have hc1 : 0 ≤ 4 * Λ ^ 2 / ν + 1 := by positivity
  have hc2 : 0 ≤ 1 / ν + 1 := by positivity
  calc ∫ y in ball x (r / 2), ‖gradient z y‖ ^ 2 ≤
      2 / ν * ((4 * Λ ^ 2 / ν + 1) * (64 / r ^ 2) * (∫ y in ball x (3 * r / 4), z y ^ 2) +
        (1 / ν + 1) * ∫ y in ball x (3 * r / 4), ‖F y‖ ^ 2) := hcac
    _ ≤ 2 / ν * ((4 * Λ ^ 2 / ν + 1) * (64 / r ^ 2) * (8 * friedrichsConst d / ν ^ 2 * r ^ 2 * f2) +
        (1 / ν + 1) * f2) := by gcongr
    _ = comparisonConst d ν Λ * f2 := by
        unfold comparisonConst
        field_simp
        ring

/-! ### Decay estimates with constant coefficients -/

theorem IsWeakDivFree.congr_ae {V W : Space d → Space d} {U : Set (Space d)}
    (h : IsWeakDivFree V U) (hVW : ∀ᵐ y, y ∈ U → V y = W y) : IsWeakDivFree W U := by
  intro ψ hψ hc hψU
  rw [← h ψ hψ hc hψU]
  apply integral_congr_ae
  filter_upwards [hVW] with y hy
  by_cases hyU : y ∈ U
  · rw [hy hyU]
  · rw [gradient_eq_zero_of_notMem_tsupport (fun h ↦ hyU (hψU h))]
    simp

theorem IsWeakDivFree.sub_const {V : Space d → Space d} {x : Space d} {r : ℝ}
    (hV : MemLp V 2 (volume.restrict (ball x r))) (h : IsWeakDivFree V (ball x r))
    (c : Space d) : IsWeakDivFree (fun y ↦ V y - c) (ball x r) := by
  rintro ψ ⟨K, hψ⟩ hc hψU
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have h1 := h ψ ⟨K, hψ⟩ hc hψU
  have h2 := integral_inner_const_gradient_eq_zero hψ hc c
  have hi1 := integrable_inner_gradient_of_memLp hV hψ hψU
  have hi2 : Integrable (fun y ↦ inner ℝ c (gradient ψ y)) :=
    integrable_inner_gradient_of_memLp (memLp_const c) hψ hψU
  have he : (fun y ↦ inner ℝ (V y - c) (gradient ψ y)) =
      fun y ↦ inner ℝ (V y) (gradient ψ y) - inner ℝ c (gradient ψ y) := by
    funext y
    exact inner_sub_left _ _ _
  rw [he, integral_sub hi1 hi2, h1, h2, sub_zero]

theorem integrableOn_norm_sq_of_le {E : Type*} [NormedAddCommGroup E] {S : Set (Space d)}
    (hS : volume S ≠ ⊤) (hSm : MeasurableSet S) {f : Space d → E}
    (hf : AEStronglyMeasurable f volume) {M : ℝ} (hM : ∀ y ∈ S, ‖f y‖ ≤ M) :
    IntegrableOn (fun y ↦ ‖f y‖ ^ 2) S :=
  Measure.integrableOn_of_bounded (M := M ^ 2) hS (hf.norm.pow 2)
    ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun y hy ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hM y hy) 2))

theorem setIntegral_norm_add_sq_le {E : Type*} [NormedAddCommGroup E]
    {S : Set (Space d)} {f g : Space d → E} (hf : IntegrableOn (fun y ↦ ‖f y‖ ^ 2) S)
    (hg : IntegrableOn (fun y ↦ ‖g y‖ ^ 2) S) :
    ∫ y in S, ‖f y + g y‖ ^ 2 ≤ 2 * (∫ y in S, ‖f y‖ ^ 2) + 2 * ∫ y in S, ‖g y‖ ^ 2 := by
  have hf' : IntegrableOn (fun y ↦ 2 * ‖f y‖ ^ 2) S := hf.const_mul 2
  have hg' : IntegrableOn (fun y ↦ 2 * ‖g y‖ ^ 2) S := hg.const_mul 2
  have h := integral_mono_of_nonneg (Eventually.of_forall fun y ↦ sq_nonneg ‖f y + g y‖)
    (hf'.add hg') (Eventually.of_forall fun y ↦ by
      have h1 := norm_add_le (f y) (g y)
      show ‖f y + g y‖ ^ 2 ≤ 2 * ‖f y‖ ^ 2 + 2 * ‖g y‖ ^ 2
      nlinarith [norm_nonneg (f y + g y), norm_nonneg (f y), norm_nonneg (g y),
        sq_nonneg (‖f y‖ - ‖g y‖)])
  have he : ∫ y in S, (2 * ‖f y‖ ^ 2 + 2 * ‖g y‖ ^ 2) =
      2 * (∫ y in S, ‖f y‖ ^ 2) + 2 * ∫ y in S, ‖g y‖ ^ 2 := by
    rw [integral_add hf' hg', integral_const_mul, integral_const_mul]
  exact h.trans_eq he

theorem memLp_fderiv_of_lipschitz {u : Space d → ℝ} {K : NNReal} (hu : LipschitzWith K u)
    (S : Set (Space d)) (hS : volume S ≠ ⊤) : MemLp (fderiv ℝ u) 2 (volume.restrict S) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS
  exact MemLp.of_bound (measurable_fderiv ℝ u).aestronglyMeasurable K
    (Eventually.of_forall fun y ↦ norm_fderiv_le_of_lipschitz ℝ hu)

/-- The constants of the excess decay estimate. -/
def excessDecayConst₁ (d : ℕ) (ν Λ : ℝ) : ℝ := 2 ^ (d + 6) * aHarmonicGradExcessConst d ν Λ

def excessDecayConst₂ (d : ℕ) (ν Λ : ℝ) : ℝ :=
  8 * comparisonConst d ν Λ + 2 ^ (d + 6) * aHarmonicGradExcessConst d ν Λ * comparisonConst d ν Λ

/-- **Excess decay with a right-hand side** (constant coefficients): for a Lipschitz weak
solution of `div (A₀ ∇u) = div F` in `B_r` and `0 < θ ≤ 1/4`,
`Ψ(θ r) ≤ C₁ θ^(d+2) Ψ(r) + C₂ ∫_{B_r} ‖F‖²`, where `Ψ(ρ) = ∫_{B_ρ} ‖Du - (Du)_{B_ρ}‖²`. -/
theorem excess_decay_of_weakDivFree (hd : 0 < d) {A₀ : Space d →L[ℝ] Space d} {ν Λ : ℝ}
    (hA : IsUniformlyElliptic A₀ ν Λ) (hbd : ‖A₀‖ ≤ Λ) {x : Space d} {r : ℝ} (hr : 0 < r)
    {F : Space d → Space d} (hF : MemLp F 2 (volume.restrict (ball x r)))
    {u : Space d → ℝ} {K : NNReal} (hu : LipschitzWith K u)
    (heq : IsWeakDivFree (fun y ↦ A₀ (gradient u y) - F y) (ball x r)) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 4) :
    ∫ y in ball x (θ * r), ‖fderiv ℝ u y - ⨍ z in ball x (θ * r), fderiv ℝ u z‖ ^ 2 ≤
      excessDecayConst₁ d ν Λ * θ ^ (d + 2) *
          (∫ y in ball x r, ‖fderiv ℝ u y - ⨍ z in ball x r, fderiv ℝ u z‖ ^ 2) +
        excessDecayConst₂ d ν Λ * ∫ y in ball x r, ‖F y‖ ^ 2 := by
  have hB : ∀ s, volume (ball x s) ≠ ⊤ := fun s ↦ measure_ball_lt_top.ne
  obtain ⟨c, hc⟩ : ∃ c, ⨍ z in ball x r, fderiv ℝ u z = c := ⟨_, rfl⟩
  rw [hc]
  obtain ⟨u', hu'⟩ : ∃ u' : Space d → ℝ, u' = fun y ↦ u y - c y := ⟨_, rfl⟩
  have hu'L : LipschitzWith (K + ‖c‖₊) u' := by
    rw [hu']
    exact hu.sub c.lipschitzWith
  have hDu' : ∀ᵐ y, fderiv ℝ u' y = fderiv ℝ u y - c := by
    filter_upwards [hu.ae_differentiableAt (μ := volume)] with y hy
    rw [hu', fderiv_fun_sub hy c.differentiableAt, c.fderiv]
  have hgu' : ∀ᵐ y, gradient u' y = gradient u y - (toDual ℝ (Space d)).symm c := by
    filter_upwards [hDu'] with y hy
    rw [gradient, hy, map_sub]
    rfl
  have : IsFiniteMeasure (volume.restrict (ball x r)) := isFiniteMeasure_restrict.2 (hB r)
  have hVL2 : MemLp (fun y ↦ A₀ (gradient u y) - F y) 2 (volume.restrict (ball x r)) := by
    refine MemLp.sub (MemLp.of_bound ?_ (‖A₀‖ * K) (Eventually.of_forall fun y ↦ ?_)) hF
    · exact (A₀.continuous.measurable.comp ((toDual ℝ (Space d)).symm.continuous.measurable.comp
        (measurable_fderiv ℝ u))).aestronglyMeasurable
    · calc ‖A₀ (gradient u y)‖ ≤ ‖A₀‖ * ‖gradient u y‖ := A₀.le_opNorm _
        _ ≤ ‖A₀‖ * K := by
          rw [norm_gradient_eq_norm_fderiv]
          exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _)
  have heq' : IsWeakDivFree (fun y ↦ A₀ (gradient u' y) - F y) (ball x r) := by
    refine (heq.sub_const hVL2 (A₀ ((toDual ℝ (Space d)).symm c))).congr_ae ?_
    filter_upwards [hgu'] with y hy _
    rw [hy, map_sub]
    abel
  obtain ⟨v, hv, hLv, hcmp⟩ :=
    exists_aHarmonic_comparison hd hA.pos hA.symm hA.lower hbd hr hF hu'L heq'
  set f2 := ∫ y in ball x r, ‖F y‖ ^ 2 with hf2
  have hf20 : 0 ≤ f2 := integral_nonneg fun _ ↦ sq_nonneg _
  set Ψr := ∫ y in ball x r, ‖fderiv ℝ u y - c‖ ^ 2 with hΨr
  have hΨr0 : 0 ≤ Ψr := integral_nonneg fun _ ↦ sq_nonneg _
  -- bounds on `Dv` on `closedBall x (r/2)`
  have hr2 : 0 < r / 2 := half_pos hr
  have hsub2 : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have hv2 : ContDiffOn ℝ 2 v (ball x r) := hv.of_le (by simp)
  have hDvc : ContinuousOn (fderiv ℝ v) (ball x r) :=
    hv2.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
  obtain ⟨Mv, hMv⟩ := (isCompact_closedBall x (r / 2)).exists_bound_of_continuousOn
    (hDvc.mono hsub2)
  have hMv0 : 0 ≤ Mv := (norm_nonneg _).trans (hMv x (mem_closedBall_self hr2.le))
  have hθr : θ * r ≤ r / 2 := by nlinarith
  -- integrability facts on `B_{r/2}`
  have hDu'm : AEStronglyMeasurable (fderiv ℝ u') volume :=
    (measurable_fderiv ℝ u').aestronglyMeasurable
  have hDvm : AEStronglyMeasurable (fderiv ℝ v) volume :=
    (measurable_fderiv ℝ v).aestronglyMeasurable
  have hi_diff : IntegrableOn (fun y ↦ ‖fderiv ℝ u' y - fderiv ℝ v y‖ ^ 2) (ball x (r / 2)) :=
    integrableOn_norm_sq_of_le (hB _) measurableSet_ball (hDu'm.sub hDvm)
      (M := (K + ‖c‖₊ : NNReal) + Mv) (fun y hy ↦ (norm_sub_le _ _).trans
        (add_le_add (norm_fderiv_le_of_lipschitz ℝ hu'L) (hMv y (ball_subset_closedBall hy))))
  have hi_Du' : IntegrableOn (fun y ↦ ‖fderiv ℝ u' y‖ ^ 2) (ball x (r / 2)) :=
    integrableOn_norm_sq_of_le (hB _) measurableSet_ball hDu'm
      (fun y _ ↦ norm_fderiv_le_of_lipschitz ℝ hu'L)
  have hi_vx : IntegrableOn (fun y ↦ ‖fderiv ℝ v y - fderiv ℝ v x‖ ^ 2) (ball x (r / 2)) :=
    integrableOn_norm_sq_of_le (hB _) measurableSet_ball (hDvm.sub aestronglyMeasurable_const)
      (M := Mv + Mv) (fun y hy ↦ (norm_sub_le _ _).trans
        (add_le_add (hMv y (ball_subset_closedBall hy)) (hMv x (mem_closedBall_self hr2.le))))
  have hi_uc : IntegrableOn (fun y ↦ ‖fderiv ℝ u y - c‖ ^ 2) (ball x r) :=
    integrableOn_norm_sq_of_le (hB _) measurableSet_ball
      (f := fun y ↦ fderiv ℝ u y - c)
      ((measurable_fderiv ℝ u).sub_const c).aestronglyMeasurable
      (M := K + ‖c‖) (fun y _ ↦ by
        have h1 := norm_sub_le (fderiv ℝ u y) c
        have h2 := norm_fderiv_le_of_lipschitz ℝ hu (x₀ := y)
        linarith)
  -- `∫_{B_{r/2}} ‖Dv‖² ≤ 2 Ψ(r) + 2 C f²`
  have hDv : ∫ y in ball x (r / 2), ‖fderiv ℝ v y‖ ^ 2 ≤
      2 * Ψr + 2 * (comparisonConst d ν Λ * f2) := by
    have h1 : ∫ y in ball x (r / 2), ‖fderiv ℝ v y‖ ^ 2 =
        ∫ y in ball x (r / 2), ‖fderiv ℝ u' y + -(fderiv ℝ u' y - fderiv ℝ v y)‖ ^ 2 := by
      congr 1
      funext y
      congr 2
      abel
    have h2 : IntegrableOn (fun y ↦ ‖-(fderiv ℝ u' y - fderiv ℝ v y)‖ ^ 2) (ball x (r / 2)) := by
      simpa only [norm_neg] using hi_diff
    have h3 := setIntegral_norm_add_sq_le hi_Du' h2
    simp only [norm_neg] at h3
    have h4 : ∫ y in ball x (r / 2), ‖fderiv ℝ u' y‖ ^ 2 ≤ Ψr := by
      have e1 : ∫ y in ball x (r / 2), ‖fderiv ℝ u' y‖ ^ 2 =
          ∫ y in ball x (r / 2), ‖fderiv ℝ u y - c‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hDu'] with y hy
        rw [hy]
      rw [e1]
      exact setIntegral_mono_set hi_uc (Eventually.of_forall fun y ↦ sq_nonneg _)
        (ball_subset_ball (by linarith)).eventuallyLE
    rw [h1]
    linarith
  -- the harmonic excess at scale `θ r`
  have hexc := aHarmonic_fderiv_excess_le hA isOpen_ball hv2 hLv hsub2 hr2
    (θ := 2 * θ) (by linarith) (by linarith)
  have hball : 2 * θ * (r / 2) = θ * r := by ring
  rw [hball] at hexc
  have hCe0 : 0 ≤ aHarmonicGradExcessConst d ν Λ := by
    unfold aHarmonicGradExcessConst
    have := aHarmonicHessGradConst_nonneg hA
    have : 0 ≤ volume.real (ball (0 : Space d) 1) := measureReal_nonneg
    positivity
  obtain ⟨Ce, hCe⟩ : ∃ Ce, Ce = aHarmonicGradExcessConst d ν Λ := ⟨_, rfl⟩
  rw [← hCe] at hexc hCe0
  -- the excess at scale `θ r`
  have hmean := setIntegral_norm_sub_setAverage_sq_le (hB (θ * r))
    (memLp_fderiv_of_lipschitz hu _ (hB _)) (c + fderiv ℝ v x)
  have hsplit : ∫ y in ball x (θ * r), ‖fderiv ℝ u y - (c + fderiv ℝ v x)‖ ^ 2 ≤
      2 * (∫ y in ball x (θ * r), ‖fderiv ℝ u' y - fderiv ℝ v y‖ ^ 2) +
        2 * ∫ y in ball x (θ * r), ‖fderiv ℝ v y - fderiv ℝ v x‖ ^ 2 := by
    have e1 : ∫ y in ball x (θ * r), ‖fderiv ℝ u y - (c + fderiv ℝ v x)‖ ^ 2 =
        ∫ y in ball x (θ * r), ‖(fderiv ℝ u' y - fderiv ℝ v y) +
          (fderiv ℝ v y - fderiv ℝ v x)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hDu'] with y hy
      rw [hy]
      congr 2
      abel
    rw [e1]
    exact setIntegral_norm_add_sq_le (hi_diff.mono_set (ball_subset_ball hθr))
      (hi_vx.mono_set (ball_subset_ball hθr))
  have hA1 : ∫ y in ball x (θ * r), ‖fderiv ℝ u' y - fderiv ℝ v y‖ ^ 2 ≤
      comparisonConst d ν Λ * f2 := by
    refine le_trans ?_ hcmp
    refine setIntegral_mono_set ?_ (Eventually.of_forall fun y ↦ sq_nonneg _)
      (ball_subset_ball hθr).eventuallyLE
    exact hi_diff
  have hA2 : ∫ y in ball x (θ * r), ‖fderiv ℝ v y - fderiv ℝ v x‖ ^ 2 ≤
      Ce * (2 * θ) ^ (d + 2) * (2 * Ψr + 2 * (comparisonConst d ν Λ * f2)) :=
    hexc.trans (mul_le_mul_of_nonneg_left hDv (by positivity))
  have hθ2 : (2 * θ) ^ (d + 2) = 2 ^ (d + 2) * θ ^ (d + 2) := mul_pow _ _ _
  have hθ1 : θ ^ (d + 2) ≤ 1 := pow_le_one₀ hθ0.le (by linarith)
  have hCc0 := comparisonConst_nonneg d hA.pos Λ
  calc ∫ y in ball x (θ * r), ‖fderiv ℝ u y - ⨍ z in ball x (θ * r), fderiv ℝ u z‖ ^ 2
      ≤ 4 * ∫ y in ball x (θ * r), ‖fderiv ℝ u y - (c + fderiv ℝ v x)‖ ^ 2 := hmean
    _ ≤ 4 * (2 * (comparisonConst d ν Λ * f2) +
          2 * (Ce * (2 * θ) ^ (d + 2) * (2 * Ψr + 2 * (comparisonConst d ν Λ * f2)))) := by
        gcongr
        exact hsplit.trans (by gcongr)
    _ = 2 ^ (d + 6) * Ce * θ ^ (d + 2) * Ψr + (8 * comparisonConst d ν Λ * f2 +
          2 ^ (d + 6) * Ce * comparisonConst d ν Λ * θ ^ (d + 2) * f2) := by
        rw [hθ2]
        ring
    _ ≤ 2 ^ (d + 6) * Ce * θ ^ (d + 2) * Ψr + (8 * comparisonConst d ν Λ * f2 +
          2 ^ (d + 6) * Ce * comparisonConst d ν Λ * 1 * f2) := by
        gcongr
    _ = excessDecayConst₁ d ν Λ * θ ^ (d + 2) * Ψr + excessDecayConst₂ d ν Λ * f2 := by
        unfold excessDecayConst₁ excessDecayConst₂
        rw [← hCe]
        ring

/-- The constants of the energy (Morrey) decay estimate. -/
def energyDecayConst₁ (d : ℕ) (ν Λ : ℝ) : ℝ :=
  4 * (2 * aHarmonicGradExcessConst d ν Λ + 2) * 8 ^ d + 4 ^ d

def energyDecayConst₂ (d : ℕ) (ν Λ : ℝ) : ℝ :=
  2 * comparisonConst d ν Λ + 4 * (2 * aHarmonicGradExcessConst d ν Λ + 2) * 8 ^ d *
    comparisonConst d ν Λ

theorem aHarmonicGradExcessConst_nonneg' {A₀ : Space d →L[ℝ] Space d} {ν Λ : ℝ}
    (hA : IsUniformlyElliptic A₀ ν Λ) : 0 ≤ aHarmonicGradExcessConst d ν Λ := by
  unfold aHarmonicGradExcessConst
  have := aHarmonicHessGradConst_nonneg hA
  have : 0 ≤ volume.real (ball (0 : Space d) 1) := measureReal_nonneg
  positivity

/-- **Energy (Morrey) decay with a right-hand side** (constant coefficients): for a Lipschitz
weak solution of `div (A₀ ∇u) = div F` in `B_r` and `0 < ρ ≤ r`,
`∫_{B_ρ} ‖Du‖² ≤ C₃ (ρ/r)^d ∫_{B_r} ‖Du‖² + C₄ ∫_{B_r} ‖F‖²`. -/
theorem energy_decay_of_weakDivFree (hd : 0 < d) {A₀ : Space d →L[ℝ] Space d} {ν Λ : ℝ}
    (hA : IsUniformlyElliptic A₀ ν Λ) (hbd : ‖A₀‖ ≤ Λ) {x : Space d} {r : ℝ} (hr : 0 < r)
    {F : Space d → Space d} (hF : MemLp F 2 (volume.restrict (ball x r)))
    {u : Space d → ℝ} {K : NNReal} (hu : LipschitzWith K u)
    (heq : IsWeakDivFree (fun y ↦ A₀ (gradient u y) - F y) (ball x r)) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρr : ρ ≤ r) :
    ∫ y in ball x ρ, ‖fderiv ℝ u y‖ ^ 2 ≤
      energyDecayConst₁ d ν Λ * (ρ / r) ^ d * (∫ y in ball x r, ‖fderiv ℝ u y‖ ^ 2) +
        energyDecayConst₂ d ν Λ * ∫ y in ball x r, ‖F y‖ ^ 2 := by
  have hB : ∀ s, volume (ball x s) ≠ ⊤ := fun s ↦ measure_ball_lt_top.ne
  set f2 := ∫ y in ball x r, ‖F y‖ ^ 2 with hf2
  have hf20 : 0 ≤ f2 := integral_nonneg fun _ ↦ sq_nonneg _
  set Φr := ∫ y in ball x r, ‖fderiv ℝ u y‖ ^ 2 with hΦr
  have hΦr0 : 0 ≤ Φr := integral_nonneg fun _ ↦ sq_nonneg _
  have hCe0 := aHarmonicGradExcessConst_nonneg' hA
  have hCc0 := comparisonConst_nonneg d hA.pos Λ
  have hC₂0 : 0 ≤ energyDecayConst₂ d ν Λ := by unfold energyDecayConst₂; positivity
  have hDu_int : ∀ s, IntegrableOn (fun y ↦ ‖fderiv ℝ u y‖ ^ 2) (ball x s) := fun s ↦
    integrableOn_norm_sq_of_le (hB _) measurableSet_ball
      (measurable_fderiv ℝ u).aestronglyMeasurable (fun y _ ↦ norm_fderiv_le_of_lipschitz ℝ hu)
  have hρr1 : ρ / r ≤ 1 := (div_le_one hr).2 hρr
  have hρr0 : 0 ≤ ρ / r := by positivity
  by_cases hρ4 : r / 4 < ρ
  · -- large `ρ`: monotonicity
    have h1 : ∫ y in ball x ρ, ‖fderiv ℝ u y‖ ^ 2 ≤ Φr :=
      setIntegral_mono_set (hDu_int r) (Eventually.of_forall fun y ↦ sq_nonneg _)
        (ball_subset_ball hρr).eventuallyLE
    have h2 : 1 ≤ 4 ^ d * (ρ / r) ^ d := by
      rw [← mul_pow]
      apply one_le_pow₀
      rw [mul_div_assoc', le_div_iff₀ hr]
      linarith
    have h3 : 4 ^ d * (ρ / r) ^ d ≤ energyDecayConst₁ d ν Λ * (ρ / r) ^ d := by
      unfold energyDecayConst₁
      have : 0 ≤ 4 * (2 * aHarmonicGradExcessConst d ν Λ + 2) * 8 ^ d * (ρ / r) ^ d := by
        positivity
      nlinarith
    calc ∫ y in ball x ρ, ‖fderiv ℝ u y‖ ^ 2 ≤ 1 * Φr := by rw [one_mul]; exact h1
      _ ≤ energyDecayConst₁ d ν Λ * (ρ / r) ^ d * Φr :=
          mul_le_mul_of_nonneg_right (h2.trans h3) hΦr0
      _ ≤ energyDecayConst₁ d ν Λ * (ρ / r) ^ d * Φr + energyDecayConst₂ d ν Λ * f2 :=
          le_add_of_nonneg_right (mul_nonneg hC₂0 hf20)
  push Not at hρ4
  obtain ⟨v, hv, hLv, hcmp⟩ :=
    exists_aHarmonic_comparison hd hA.pos hA.symm hA.lower hbd hr hF hu heq
  have hr2 : 0 < r / 2 := half_pos hr
  have hsub2 : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have hv2 : ContDiffOn ℝ 2 v (ball x r) := hv.of_le (by simp)
  have hDvc : ContinuousOn (fderiv ℝ v) (ball x r) :=
    hv2.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
  obtain ⟨Mv, hMv⟩ := (isCompact_closedBall x (r / 2)).exists_bound_of_continuousOn
    (hDvc.mono hsub2)
  have hDvm : AEStronglyMeasurable (fderiv ℝ v) volume :=
    (measurable_fderiv ℝ v).aestronglyMeasurable
  have hi_v : ∀ s, s ≤ r / 2 → IntegrableOn (fun y ↦ ‖fderiv ℝ v y‖ ^ 2) (ball x s) :=
    fun s hs ↦ integrableOn_norm_sq_of_le (hB _) measurableSet_ball hDvm
      (fun y hy ↦ hMv y (ball_subset_closedBall (ball_subset_ball hs hy)))
  have hi_diff : IntegrableOn (fun y ↦ ‖fderiv ℝ u y - fderiv ℝ v y‖ ^ 2) (ball x (r / 2)) :=
    integrableOn_norm_sq_of_le (hB _) measurableSet_ball
      (f := fun y ↦ fderiv ℝ u y - fderiv ℝ v y)
      ((measurable_fderiv ℝ u).sub (measurable_fderiv ℝ v)).aestronglyMeasurable
      (M := K + Mv) (fun y hy ↦ by
        have h1 := norm_sub_le (fderiv ℝ u y) (fderiv ℝ v y)
        have h2 := norm_fderiv_le_of_lipschitz ℝ hu (x₀ := y)
        have h3 := hMv y (ball_subset_closedBall hy)
        linarith)
  set I := ∫ y in ball x (r / 2), ‖fderiv ℝ v y‖ ^ 2 with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ ↦ sq_nonneg _
  -- `I ≤ 2 Φ(r) + 2 C f²`
  have hDv : I ≤ 2 * Φr + 2 * (comparisonConst d ν Λ * f2) := by
    have h1 : I = ∫ y in ball x (r / 2), ‖fderiv ℝ u y + -(fderiv ℝ u y - fderiv ℝ v y)‖ ^ 2 := by
      rw [hI]
      congr 1
      funext y
      congr 2
      abel
    have h2 : IntegrableOn (fun y ↦ ‖-(fderiv ℝ u y - fderiv ℝ v y)‖ ^ 2) (ball x (r / 2)) := by
      simpa only [norm_neg] using hi_diff
    have h3 := setIntegral_norm_add_sq_le (hDu_int (r / 2)) h2
    simp only [norm_neg] at h3
    have h4 : ∫ y in ball x (r / 2), ‖fderiv ℝ u y‖ ^ 2 ≤ Φr :=
      setIntegral_mono_set (hDu_int r) (Eventually.of_forall fun y ↦ sq_nonneg _)
        (ball_subset_ball (by linarith)).eventuallyLE
    rw [h1]
    linarith
  -- pointwise bound on `‖Dv‖²` in `B_{r/4}`
  set ωd := volume.real (ball (0 : Space d) 1) with hωd
  have hωd0 : 0 < ωd := measureReal_unitBall_pos
  have hpt : ∀ y ∈ ball x (r / 4), ‖fderiv ℝ v y‖ ^ 2 ≤
      (2 * aHarmonicGradExcessConst d ν Λ + 2) * I / ((r / 8) ^ d * ωd) := by
    intro y hy
    have hr8 : 0 < r / 8 := by positivity
    have hr4 : 0 < r / 4 := by positivity
    have hsuby : closedBall y (r / 4) ⊆ ball x (r / 2) := by
      intro z hz
      rw [mem_closedBall] at hz
      rw [mem_ball] at hy ⊢
      linarith [dist_triangle z y x]
    have hexc := aHarmonic_fderiv_excess_le hA isOpen_ball hv2 hLv
      (hsuby.trans (ball_subset_ball (by linarith))) hr4 (θ := 1 / 2) (by norm_num) le_rfl
    have hball : 1 / 2 * (r / 4) = r / 8 := by ring
    rw [hball] at hexc
    have hsub8 : ball y (r / 8) ⊆ ball x (r / 2) :=
      (ball_subset_ball (by linarith)).trans (ball_subset_closedBall.trans hsuby)
    have hIy : ∫ z in ball y (r / 4), ‖fderiv ℝ v z‖ ^ 2 ≤ I :=
      setIntegral_mono_set (hi_v (r / 2) le_rfl) (Eventually.of_forall fun y ↦ sq_nonneg _)
        (ball_subset_closedBall.trans hsuby).eventuallyLE
    have hhalf : (1 / 2 : ℝ) ^ (d + 2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hA1 : ∫ z in ball y (r / 8), ‖fderiv ℝ v z - fderiv ℝ v y‖ ^ 2 ≤
        aHarmonicGradExcessConst d ν Λ * I := by
      refine hexc.trans ?_
      calc aHarmonicGradExcessConst d ν Λ * (1 / 2) ^ (d + 2) *
            ∫ z in ball y (r / 4), ‖fderiv ℝ v z‖ ^ 2 ≤
          aHarmonicGradExcessConst d ν Λ * 1 * I := by gcongr
        _ = aHarmonicGradExcessConst d ν Λ * I := by ring
    have hMy : ‖fderiv ℝ v y‖ ≤ Mv :=
      hMv y (ball_subset_closedBall (ball_subset_ball (by linarith) hy))
    have hi1 : IntegrableOn (fun z ↦ ‖fderiv ℝ v z - fderiv ℝ v y‖ ^ 2) (ball y (r / 8)) :=
      integrableOn_norm_sq_of_le measure_ball_lt_top.ne measurableSet_ball
        (hDvm.sub aestronglyMeasurable_const) (M := Mv + Mv) (fun z hz ↦ by
          have h1 := norm_sub_le (fderiv ℝ v z) (fderiv ℝ v y)
          have h2 := hMv z (ball_subset_closedBall (hsub8 hz))
          linarith)
    have hi2 : IntegrableOn (fun z ↦ ‖fderiv ℝ v z‖ ^ 2) (ball y (r / 8)) :=
      (hi_v (r / 2) le_rfl).mono_set hsub8
    have hconst : ∫ z in ball y (r / 8), ‖fderiv ℝ v y‖ ^ 2 =
        (r / 8) ^ d * ωd * ‖fderiv ℝ v y‖ ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, measureReal_ball_eq_mul y hr8]
    have hsplit : ∫ z in ball y (r / 8), ‖fderiv ℝ v y‖ ^ 2 ≤
        2 * (∫ z in ball y (r / 8), ‖fderiv ℝ v z - fderiv ℝ v y‖ ^ 2) +
          2 * ∫ z in ball y (r / 8), ‖fderiv ℝ v z‖ ^ 2 := by
      have h1 : ∫ z in ball y (r / 8), ‖fderiv ℝ v y‖ ^ 2 =
          ∫ z in ball y (r / 8), ‖-(fderiv ℝ v z - fderiv ℝ v y) + fderiv ℝ v z‖ ^ 2 := by
        congr 1
        funext z
        congr 2
        abel
      have h2 : IntegrableOn (fun z ↦ ‖-(fderiv ℝ v z - fderiv ℝ v y)‖ ^ 2) (ball y (r / 8)) := by
        simpa only [norm_neg] using hi1
      have h3 := setIntegral_norm_add_sq_le h2 hi2
      simp only [norm_neg] at h3
      rw [h1]
      exact h3
    have hI8 : ∫ z in ball y (r / 8), ‖fderiv ℝ v z‖ ^ 2 ≤ I :=
      setIntegral_mono_set (hi_v (r / 2) le_rfl) (Eventually.of_forall fun y ↦ sq_nonneg _)
        hsub8.eventuallyLE
    have hpos : 0 < (r / 8) ^ d * ωd := by positivity
    rw [le_div_iff₀ hpos]
    rw [hconst] at hsplit
    nlinarith
  -- integrate the pointwise bound over `B_ρ`
  have hρ4' : ρ ≤ r / 4 := hρ4
  have hvρ : ∫ y in ball x ρ, ‖fderiv ℝ v y‖ ^ 2 ≤
      (2 * aHarmonicGradExcessConst d ν Λ + 2) * 8 ^ d * (ρ / r) ^ d * I := by
    have h1 : ∫ y in ball x ρ, ‖fderiv ℝ v y‖ ^ 2 ≤
        ∫ y in ball x ρ, (2 * aHarmonicGradExcessConst d ν Λ + 2) * I / ((r / 8) ^ d * ωd) :=
      setIntegral_mono_on (hi_v ρ (by linarith)) (integrableOn_const measure_ball_lt_top.ne)
        measurableSet_ball (fun y hy ↦ hpt y (ball_subset_ball hρ4' hy))
    rw [setIntegral_const, smul_eq_mul, measureReal_ball_eq_mul x hρ0] at h1
    refine h1.trans_eq ?_
    rw [div_pow, div_pow]
    field_simp
    ring
  -- conclusion
  have hi_v' := hi_v ρ (by linarith)
  have hi_diff' : IntegrableOn (fun y ↦ ‖fderiv ℝ u y - fderiv ℝ v y‖ ^ 2) (ball x ρ) :=
    hi_diff.mono_set (ball_subset_ball (by linarith))
  have hsplit : ∫ y in ball x ρ, ‖fderiv ℝ u y‖ ^ 2 ≤
      2 * (∫ y in ball x ρ, ‖fderiv ℝ u y - fderiv ℝ v y‖ ^ 2) +
        2 * ∫ y in ball x ρ, ‖fderiv ℝ v y‖ ^ 2 := by
    have h1 : ∫ y in ball x ρ, ‖fderiv ℝ u y‖ ^ 2 =
        ∫ y in ball x ρ, ‖(fderiv ℝ u y - fderiv ℝ v y) + fderiv ℝ v y‖ ^ 2 := by
      congr 1
      funext y
      congr 2
      abel
    rw [h1]
    exact setIntegral_norm_add_sq_le hi_diff' hi_v'
  have hcmpρ : ∫ y in ball x ρ, ‖fderiv ℝ u y - fderiv ℝ v y‖ ^ 2 ≤
      comparisonConst d ν Λ * f2 :=
    (setIntegral_mono_set hi_diff (Eventually.of_forall fun y ↦ sq_nonneg _)
      (ball_subset_ball (by linarith)).eventuallyLE).trans hcmp
  have hpow : (ρ / r) ^ d ≤ 1 := pow_le_one₀ hρr0 hρr1
  have hK8 : 0 ≤ (2 * aHarmonicGradExcessConst d ν Λ + 2) * 8 ^ d := by positivity
  calc ∫ y in ball x ρ, ‖fderiv ℝ u y‖ ^ 2 ≤
      2 * (comparisonConst d ν Λ * f2) +
        2 * ((2 * aHarmonicGradExcessConst d ν Λ + 2) * 8 ^ d * (ρ / r) ^ d *
          (2 * Φr + 2 * (comparisonConst d ν Λ * f2))) := by
        refine hsplit.trans ?_
        gcongr
        exact hvρ.trans (by gcongr)
    _ = 4 * (2 * aHarmonicGradExcessConst d ν Λ + 2) * 8 ^ d * (ρ / r) ^ d * Φr +
        (2 * comparisonConst d ν Λ * f2 + 4 * (2 * aHarmonicGradExcessConst d ν Λ + 2) * 8 ^ d *
          (ρ / r) ^ d * comparisonConst d ν Λ * f2) := by ring
    _ ≤ energyDecayConst₁ d ν Λ * (ρ / r) ^ d * Φr +
        (2 * comparisonConst d ν Λ * f2 + 4 * (2 * aHarmonicGradExcessConst d ν Λ + 2) * 8 ^ d *
          1 * comparisonConst d ν Λ * f2) := by
        gcongr
        · unfold energyDecayConst₁
          have : (0 : ℝ) ≤ 4 ^ d := by positivity
          linarith
    _ = energyDecayConst₁ d ν Λ * (ρ / r) ^ d * Φr + energyDecayConst₂ d ν Λ * f2 := by
        unfold energyDecayConst₂
        ring

/-! ### Frozen coefficients -/

theorem isUniformlyElliptic_of_bounds (hd : 0 < d) {A : Space d →L[ℝ] Space d} {ν Λ : ℝ}
    (hν : 0 < ν) (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    (hell : ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) (hbd : ‖A‖ ≤ Λ) : IsUniformlyElliptic A ν Λ where
  symm := hsymm
  pos := hν
  le := by
    obtain ⟨e, he⟩ : ∃ e : Space d, ‖e‖ = 1 :=
      ⟨EuclideanSpace.single ⟨0, hd⟩ 1, by simp⟩
    have h1 := hell e
    have h2 : inner ℝ (A e) e ≤ Λ := by
      calc inner ℝ (A e) e ≤ ‖A e‖ * ‖e‖ := real_inner_le_norm _ _
        _ ≤ ‖A‖ * ‖e‖ * ‖e‖ := by gcongr; exact A.le_opNorm e
        _ ≤ Λ := by rw [he, mul_one, mul_one]; exact hbd
    rw [he] at h1
    linarith
  lower := hell
  upper := fun ξ ↦ by
    calc inner ℝ (A ξ) ξ ≤ ‖A ξ‖ * ‖ξ‖ := real_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖ξ‖ * ‖ξ‖ := by gcongr; exact A.le_opNorm ξ
      _ ≤ Λ * ‖ξ‖ ^ 2 := by rw [sq, ← mul_assoc]; gcongr

private theorem measurable_gradient_aux'' (f : Space d → ℝ) : Measurable (gradient f) :=
  (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

/-- The weak equation with coefficients frozen at the center `x`:
`div (a(x) ∇w) = div F_x`, `F_x = (a(x) - a) ∇w + G - G(x)`. -/
theorem frozen_weakDivFree {a : Space d → Space d →L[ℝ] Space d} {G : Space d → Space d}
    {w : Space d → ℝ} {K : NNReal} (hw : LipschitzWith K w) {x₀ : Space d} {R Λ : ℝ}
    (ha : ContinuousOn a (ball x₀ R)) (hG : ContinuousOn G (ball x₀ R))
    (hbd : ∀ y ∈ ball x₀ R, ‖a y‖ ≤ Λ)
    (heq : IsWeakDivFree (fun y ↦ a y (gradient w y) - G y) (ball x₀ R))
    {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ ball x₀ R) :
    IsWeakDivFree (fun y ↦ a x (gradient w y) - ((a x - a y) (gradient w y) + (G y - G x)))
      (ball x r) := by
  have hsub : ball x r ⊆ ball x₀ R := ball_subset_closedBall.trans hxr
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨MG, hMG⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn (hG.mono hxr)
  have hV : MemLp (fun y ↦ a y (gradient w y) - G y) 2 (volume.restrict (ball x r)) := by
    refine MemLp.of_bound ?_ (Λ * K + MG) ?_
    · exact ((ContinuousLinearMap.id ℝ (Space d →L[ℝ] Space d)).aestronglyMeasurable_comp₂
        ((ha.mono hsub).aestronglyMeasurable measurableSet_ball)
        (measurable_gradient_aux'' w).aestronglyMeasurable).sub
        ((hG.mono hsub).aestronglyMeasurable measurableSet_ball)
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hbd y (hsub hy))
      have h1 : ‖a y (gradient w y)‖ ≤ Λ * K :=
        ((a y).le_opNorm _).trans (mul_le_mul (hbd y (hsub hy))
          (by rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hw)
          (norm_nonneg _) hΛ0)
      have h2 := hMG y (ball_subset_closedBall hy)
      calc ‖a y (gradient w y) - G y‖ ≤ ‖a y (gradient w y)‖ + ‖G y‖ := norm_sub_le _ _
        _ ≤ Λ * K + MG := add_le_add h1 h2
  refine ((heq.mono hsub).sub_const hV (-G x)).congr_ae (Eventually.of_forall fun y _ ↦ ?_)
  simp only [sub_apply]
  abel

/-- The right-hand side `F_x = (a(x) - a) ∇w + G - G(x)` is in `L²(B_r(x))` with
`∫_{B_r} ‖F_x‖² ≤ 2 H² r^(2α) ∫_{B_r} ‖Dw‖² + 2 HG² |B_1| r^(d + 2α)`. -/
theorem frozen_rhs_bound {a : Space d → Space d →L[ℝ] Space d} {G : Space d → Space d}
    {w : Space d → ℝ} {K : NNReal} (hw : LipschitzWith K w) {x₀ : Space d} {R H HG α : ℝ}
    (hα : 0 < α) (hH : 0 ≤ H) (hHG : 0 ≤ HG)
    (ha : ContinuousOn a (ball x₀ R)) (hG : ContinuousOn G (ball x₀ R))
    (ha_hol : ∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R, ‖a y - a y'‖ ≤ H * dist y y' ^ α)
    (hG_hol : ∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R, ‖G y - G y'‖ ≤ HG * dist y y' ^ α)
    {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ ball x₀ R) (hr : 0 < r) :
    MemLp (fun y ↦ (a x - a y) (gradient w y) + (G y - G x)) 2 (volume.restrict (ball x r)) ∧
    ∫ y in ball x r, ‖(a x - a y) (gradient w y) + (G y - G x)‖ ^ 2 ≤
      2 * H ^ 2 * r ^ (2 * α) * (∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2) +
        2 * HG ^ 2 * volume.real (ball (0 : Space d) 1) * r ^ ((d : ℝ) + 2 * α) := by
  have hsub : ball x r ⊆ ball x₀ R := ball_subset_closedBall.trans hxr
  have hx : x ∈ ball x₀ R := hxr (mem_closedBall_self hr.le)
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hrα : 0 ≤ r ^ α := Real.rpow_nonneg hr.le α
  have hpt : ∀ y ∈ ball x r, ‖(a x - a y) (gradient w y) + (G y - G x)‖ ≤
      H * r ^ α * ‖fderiv ℝ w y‖ + HG * r ^ α := by
    intro y hy
    have hdy : dist y x ^ α ≤ r ^ α :=
      Real.rpow_le_rpow dist_nonneg (mem_ball.1 hy).le hα.le
    have h1 : ‖a x - a y‖ ≤ H * r ^ α := by
      refine (ha_hol x hx y (hsub hy)).trans ?_
      rw [dist_comm]
      exact mul_le_mul_of_nonneg_left hdy hH
    have h2 : ‖G y - G x‖ ≤ HG * r ^ α :=
      (hG_hol y (hsub hy) x hx).trans (mul_le_mul_of_nonneg_left hdy hHG)
    have h3 : ‖(a x - a y) (gradient w y)‖ ≤ H * r ^ α * ‖fderiv ℝ w y‖ := by
      refine ((a x - a y).le_opNorm _).trans ?_
      rw [norm_gradient_eq_norm_fderiv]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    exact (norm_add_le _ _).trans (add_le_add h3 h2)
  have hm : AEStronglyMeasurable (fun y ↦ (a x - a y) (gradient w y) + (G y - G x))
      (volume.restrict (ball x r)) := by
    have ha' : AEStronglyMeasurable (fun y ↦ a x - a y) (volume.restrict (ball x r)) :=
      aestronglyMeasurable_const.sub ((ha.mono hsub).aestronglyMeasurable measurableSet_ball)
    exact ((ContinuousLinearMap.id ℝ (Space d →L[ℝ] Space d)).aestronglyMeasurable_comp₂ ha'
      (measurable_gradient_aux'' w).aestronglyMeasurable).add
      (((hG.mono hsub).aestronglyMeasurable measurableSet_ball).sub aestronglyMeasurable_const)
  have hmem : MemLp (fun y ↦ (a x - a y) (gradient w y) + (G y - G x)) 2
      (volume.restrict (ball x r)) := by
    refine MemLp.of_bound hm (H * r ^ α * K + HG * r ^ α) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    refine (hpt y hy).trans ?_
    have := norm_fderiv_le_of_lipschitz ℝ hw (x₀ := y)
    have h0 : 0 ≤ H * r ^ α := mul_nonneg hH hrα
    nlinarith
  refine ⟨hmem, ?_⟩
  have hr2 : (r ^ α) ^ 2 = r ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    ring_nf
  have hpt2 : ∀ y ∈ ball x r, ‖(a x - a y) (gradient w y) + (G y - G x)‖ ^ 2 ≤
      2 * H ^ 2 * r ^ (2 * α) * ‖fderiv ℝ w y‖ ^ 2 + 2 * HG ^ 2 * r ^ (2 * α) := by
    intro y hy
    have h := hpt y hy
    have h0 := norm_nonneg ((a x - a y) (gradient w y) + (G y - G x))
    have h1 : ‖(a x - a y) (gradient w y) + (G y - G x)‖ ^ 2 ≤
        (H * r ^ α * ‖fderiv ℝ w y‖ + HG * r ^ α) ^ 2 := pow_le_pow_left₀ h0 h 2
    have h2 : (H * r ^ α * ‖fderiv ℝ w y‖ + HG * r ^ α) ^ 2 ≤
        2 * (H * r ^ α * ‖fderiv ℝ w y‖) ^ 2 + 2 * (HG * r ^ α) ^ 2 := by
      nlinarith [sq_nonneg (H * r ^ α * ‖fderiv ℝ w y‖ - HG * r ^ α)]
    have h3 : 2 * (H * r ^ α * ‖fderiv ℝ w y‖) ^ 2 + 2 * (HG * r ^ α) ^ 2 =
        2 * H ^ 2 * r ^ (2 * α) * ‖fderiv ℝ w y‖ ^ 2 + 2 * HG ^ 2 * r ^ (2 * α) := by
      rw [mul_pow, mul_pow, mul_pow, hr2]
      ring
    linarith
  have hiD : IntegrableOn (fun y ↦ ‖fderiv ℝ w y‖ ^ 2) (ball x r) :=
    Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) measure_ball_lt_top.ne
      ((measurable_fderiv ℝ w).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hw) 2)
  have hiR : IntegrableOn (fun y ↦ 2 * H ^ 2 * r ^ (2 * α) * ‖fderiv ℝ w y‖ ^ 2 +
      2 * HG ^ 2 * r ^ (2 * α)) (ball x r) :=
    (hiD.const_mul _).add (integrableOn_const measure_ball_lt_top.ne)
  have h1 : ∫ y in ball x r, ‖(a x - a y) (gradient w y) + (G y - G x)‖ ^ 2 ≤
      ∫ y in ball x r, (2 * H ^ 2 * r ^ (2 * α) * ‖fderiv ℝ w y‖ ^ 2 + 2 * HG ^ 2 * r ^ (2 * α)) :=
    setIntegral_mono_on hmem.norm.integrable_sq hiR measurableSet_ball hpt2
  rw [integral_add (hiD.const_mul _) (integrableOn_const measure_ball_lt_top.ne),
    integral_const_mul, setIntegral_const, smul_eq_mul, measureReal_ball_eq_mul x hr] at h1
  refine h1.trans_eq ?_
  rw [Real.rpow_add hr, Real.rpow_natCast]
  ring

/-! ### The Schauder estimate for Hölder coefficients -/

theorem continuousOn_of_holder {E : Type*} [NormedAddCommGroup E] {f : Space d → E}
    {U : Set (Space d)} {H α : ℝ} (hα : 0 < α)
    (hf : ∀ y ∈ U, ∀ y' ∈ U, ‖f y - f y'‖ ≤ H * dist y y' ^ α) : ContinuousOn f U := by
  intro y hy
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hd0 : Tendsto (fun y' ↦ dist y' y) (𝓝 y) (𝓝 0) := by
    have := (continuous_id.dist (continuous_const : Continuous fun _ : Space d ↦ y)).tendsto y
    simpa using this
  have hpow : Tendsto (fun y' ↦ H * dist y' y ^ α) (𝓝 y) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto).comp hd0
    simpa [Real.zero_rpow hα.ne'] using this.const_mul H
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_nhdsWithin_of_tendsto_nhds hpow)
  filter_upwards [self_mem_nhdsWithin] with y' hy'
  exact hf y' hy' y hy

theorem isUniformlyElliptic_smul_id (hd : 0 < d) {ν Λ : ℝ} (hν : 0 < ν) (hνΛ : ν ≤ Λ) :
    IsUniformlyElliptic (Λ • ContinuousLinearMap.id ℝ (Space d)) ν Λ := by
  have hΛ : 0 ≤ Λ := hν.le.trans hνΛ
  refine isUniformlyElliptic_of_bounds hd hν (fun u v ↦ ?_) (fun ξ ↦ ?_) ?_
  · simp [inner_smul_left, inner_smul_right]
  · simp only [smul_apply, ContinuousLinearMap.id_apply, inner_smul_left,
      real_inner_self_eq_norm_sq, RCLike.conj_to_real]
    exact mul_le_mul_of_nonneg_right hνΛ (sq_nonneg _)
  · refine ContinuousLinearMap.opNorm_le_bound _ hΛ (fun v ↦ ?_)
    rw [smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_of_nonneg hΛ]

/-! ### The two iteration lemmas -/

/-- **Perturbed Morrey iteration.** -/
theorem morrey_iteration (hd : 0 < d) {α C₃ C₄ H R : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC₃ : 1 ≤ C₃) (hC₄ : 0 ≤ C₄) (hR : 0 < R) :
    ∃ KM r₁ : ℝ, 0 ≤ KM ∧ 0 < r₁ ∧ r₁ ≤ R ∧
      ∀ (Φ : ℝ → ℝ) (A : ℝ), 0 ≤ A → (∀ s, 0 ≤ Φ s) → (∀ s t, s ≤ t → Φ s ≤ Φ t) →
        (∀ ρ s, 0 < ρ → ρ ≤ s → s ≤ R → Φ ρ ≤ C₃ * (ρ / s) ^ d * Φ s +
          C₄ * (2 * H ^ 2 * s ^ (2 * α) * Φ s + A * s ^ ((d : ℝ) + 2 * α))) →
        ∀ s, 0 < s → s ≤ r₁ → Φ s ≤ KM * (s / r₁) ^ ((d : ℝ) - α) *
          (Φ r₁ + (C₄ * A) * r₁ ^ ((d : ℝ) + 2 * α)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hb0 : 0 < 1 / (2 * C₃) := by positivity
  have hb1 : 1 / (2 * C₃) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨θM, hθM⟩ : ∃ t : ℝ, t = (1 / (2 * C₃)) ^ (1 / α) := ⟨_, rfl⟩
  have hθM0 : 0 < θM := hθM ▸ Real.rpow_pos_of_pos hb0 _
  have hθM1 : θM < 1 := hθM ▸ Real.rpow_lt_one hb0.le hb1 (by positivity)
  have hθMα : θM ^ α = 1 / (2 * C₃) := by
    rw [hθM, ← Real.rpow_mul hb0.le, one_div_mul_cancel hα0.ne', Real.rpow_one]
  obtain ⟨σM, hσM⟩ : ∃ t : ℝ, t = (d : ℝ) - α := ⟨_, rfl⟩
  obtain ⟨τM, hτM⟩ : ∃ t : ℝ, t = (d : ℝ) + 2 * α := ⟨_, rfl⟩
  have hσM0 : 0 ≤ σM := by rw [hσM]; linarith
  have hστM : σM < τM := by rw [hσM, hτM]; linarith
  have hθMσ0 : 0 < θM ^ σM := Real.rpow_pos_of_pos hθM0 _
  have hq0 : 0 < θM ^ σM / (4 * C₄ * H ^ 2 + 1) := by positivity
  obtain ⟨r₁, hr₁⟩ : ∃ r : ℝ,
      r = min R ((θM ^ σM / (4 * C₄ * H ^ 2 + 1)) ^ (1 / (2 * α))) := ⟨_, rfl⟩
  have hr₁0 : 0 < r₁ := by
    rw [hr₁]
    exact lt_min hR (Real.rpow_pos_of_pos hq0 _)
  have hr₁R : r₁ ≤ R := hr₁ ▸ min_le_left _ _
  have hr₁H : ∀ s, 0 < s → s ≤ r₁ → C₄ * (2 * H ^ 2 * s ^ (2 * α)) ≤ θM ^ σM / 2 := by
    intro s hs hsr
    have h1 : s ≤ (θM ^ σM / (4 * C₄ * H ^ 2 + 1)) ^ (1 / (2 * α)) :=
      hsr.trans (hr₁ ▸ min_le_right _ _)
    have h2 : s ^ (2 * α) ≤ θM ^ σM / (4 * C₄ * H ^ 2 + 1) := by
      calc s ^ (2 * α) ≤ ((θM ^ σM / (4 * C₄ * H ^ 2 + 1)) ^ (1 / (2 * α))) ^ (2 * α) :=
            Real.rpow_le_rpow hs.le h1 (by positivity)
        _ = θM ^ σM / (4 * C₄ * H ^ 2 + 1) := by
            rw [← Real.rpow_mul hq0.le, one_div_mul_cancel (by positivity), Real.rpow_one]
    rw [le_div_iff₀ (by positivity)] at h2
    have hs2 : 0 ≤ s ^ (2 * α) := Real.rpow_nonneg hs.le _
    have hCH : 0 ≤ C₄ * H ^ 2 * s ^ (2 * α) := by positivity
    nlinarith
  have hθMστ : 0 < θM ^ σM - θM ^ τM :=
    sub_pos.2 (Real.rpow_lt_rpow_of_exponent_gt hθM0 hθM1 hστM)
  refine ⟨1 / (θM ^ σM * (θM ^ σM - θM ^ τM)), r₁, by positivity, hr₁0, hr₁R, ?_⟩
  intro Φ A hA hΦ0 hΦmono hdec s hs hsr
  have hratio : C₃ * θM ^ d = θM ^ σM / 2 := by
    have h1 : θM ^ d = θM ^ σM * θM ^ α := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hθM0, hσM, show (d : ℝ) - α + α = (d : ℝ) by ring]
    rw [h1, hθMα]
    field_simp
  have hdecM : ∀ t, 0 < t → t ≤ r₁ → Φ (θM * t) ≤ θM ^ σM * Φ t + (C₄ * A) * t ^ τM := by
    intro t ht htr
    have h := hdec (θM * t) t (mul_pos hθM0 ht) (mul_le_of_le_one_left ht.le hθM1.le)
      (htr.trans hr₁R)
    rw [mul_div_assoc, div_self ht.ne', mul_one, hratio] at h
    have hH' := hr₁H t ht htr
    have hΦt := hΦ0 t
    have hτ : t ^ ((d : ℝ) + 2 * α) = t ^ τM := by rw [hτM]
    rw [hτ] at h
    have h2 : C₄ * (2 * H ^ 2 * t ^ (2 * α)) * Φ t ≤ θM ^ σM / 2 * Φ t :=
      mul_le_mul_of_nonneg_right hH' hΦt
    calc Φ (θM * t) ≤ θM ^ σM / 2 * Φ t +
          C₄ * (2 * H ^ 2 * t ^ (2 * α) * Φ t + A * t ^ τM) := h
      _ = θM ^ σM / 2 * Φ t + C₄ * (2 * H ^ 2 * t ^ (2 * α)) * Φ t + (C₄ * A) * t ^ τM := by
          ring
      _ ≤ θM ^ σM / 2 * Φ t + θM ^ σM / 2 * Φ t + (C₄ * A) * t ^ τM := by linarith only [h2]
      _ = θM ^ σM * Φ t + (C₄ * A) * t ^ τM := by ring
  have h := le_of_excess_decay (ψ := Φ) hθM0 hθM1 hσM0 hστM zero_le_one
    (A := C₄ * A) (mul_nonneg hC₄ hA) hr₁0 (hΦ0 r₁)
    (fun s t _ _ hst _ ↦ by rw [one_mul]; exact hΦmono s t hst) hdecM hs hsr
  rw [hσM, hτM] at h ⊢
  exact h

/-- **Perturbed Campanato iteration.** -/
theorem campanato_iteration {α C₁ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hC₁ : 0 ≤ C₁) :
    ∃ KC θC : ℝ, 0 ≤ KC ∧ 0 < θC ∧ θC ≤ 1 / 4 ∧
      ∀ (Ψ : ℝ → ℝ) (B r₁ : ℝ), 0 ≤ B → 0 < r₁ → (∀ s, 0 ≤ Ψ s) →
        (∀ s t, 0 < s → s ≤ t → Ψ s ≤ 4 * Ψ t) →
        (∀ s, 0 < s → s ≤ r₁ → Ψ (θC * s) ≤ C₁ * θC ^ (d + 2) * Ψ s +
          B * s ^ ((d : ℝ) + α)) →
        ∀ s, 0 < s → s ≤ r₁ → Ψ s ≤ KC * (s / r₁) ^ ((d : ℝ) + α / 2) *
          (Ψ r₁ + B * r₁ ^ ((d : ℝ) + α)) := by
  have hθb0 : 0 < (1 / (C₁ + 1)) ^ (1 / (2 - α / 2)) := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨θC, hθC⟩ : ∃ t : ℝ, t = min (1 / 4) ((1 / (C₁ + 1)) ^ (1 / (2 - α / 2))) :=
    ⟨_, rfl⟩
  have hθC0 : 0 < θC := by rw [hθC]; exact lt_min (by norm_num) hθb0
  have hθC14 : θC ≤ 1 / 4 := hθC ▸ min_le_left _ _
  have hθC1 : θC < 1 := by linarith
  have hθCkey : C₁ * θC ^ (d + 2) ≤ θC ^ ((d : ℝ) + α / 2) := by
    have h2α : 0 < 2 - α / 2 := by linarith
    have h1 : θC ^ (d + 2) = θC ^ ((d : ℝ) + α / 2) * θC ^ (2 - α / 2) := by
      rw [← Real.rpow_add hθC0, ← Real.rpow_natCast,
        show (d : ℝ) + α / 2 + (2 - α / 2) = ((d + 2 : ℕ) : ℝ) by push_cast; ring]
    have h2 : θC ^ (2 - α / 2) ≤ 1 / (C₁ + 1) := by
      calc θC ^ (2 - α / 2) ≤ ((1 / (C₁ + 1)) ^ (1 / (2 - α / 2))) ^ (2 - α / 2) :=
            Real.rpow_le_rpow hθC0.le (hθC ▸ min_le_right _ _) h2α.le
        _ = 1 / (C₁ + 1) := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel h2α.ne', Real.rpow_one]
    have h3 : C₁ * θC ^ (2 - α / 2) ≤ 1 := by
      calc C₁ * θC ^ (2 - α / 2) ≤ C₁ * (1 / (C₁ + 1)) := mul_le_mul_of_nonneg_left h2 hC₁
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]
            linarith
    have h4 : 0 ≤ θC ^ ((d : ℝ) + α / 2) := Real.rpow_nonneg hθC0.le _
    rw [h1]
    nlinarith
  have hστC : (d : ℝ) + α / 2 < (d : ℝ) + α := by linarith
  have hθCστ : 0 < θC ^ ((d : ℝ) + α / 2) - θC ^ ((d : ℝ) + α) :=
    sub_pos.2 (Real.rpow_lt_rpow_of_exponent_gt hθC0 hθC1 hστC)
  have hθCσ : 0 < θC ^ ((d : ℝ) + α / 2) := Real.rpow_pos_of_pos hθC0 _
  refine ⟨4 / (θC ^ ((d : ℝ) + α / 2) * (θC ^ ((d : ℝ) + α / 2) - θC ^ ((d : ℝ) + α))), θC,
    by positivity, hθC0, hθC14, ?_⟩
  intro Ψ B r₁ hB hr₁ hΨ0 hΨmono hdec s hs hsr
  have hdec' : ∀ t, 0 < t → t ≤ r₁ →
      Ψ (θC * t) ≤ θC ^ ((d : ℝ) + α / 2) * Ψ t + B * t ^ ((d : ℝ) + α) := by
    intro t ht htr
    have h := hdec t ht htr
    have h2 := mul_le_mul_of_nonneg_right hθCkey (hΨ0 t)
    linarith only [h, h2]
  exact le_of_excess_decay (ψ := Ψ) hθC0 hθC1 (by positivity) hστC (K := 4) (by norm_num)
    (A := B) hB hr₁ (hΨ0 r₁) (fun s t hs _ hst _ ↦ hΨmono s t hs hst) hdec' hs hsr

/-! ### Decay at a center for Hölder coefficients -/

theorem energyDecayConst₂_nonneg {A₀ : Space d →L[ℝ] Space d} {ν Λ : ℝ}
    (hA : IsUniformlyElliptic A₀ ν Λ) : 0 ≤ energyDecayConst₂ d ν Λ := by
  have := aHarmonicGradExcessConst_nonneg' hA
  have := comparisonConst_nonneg d hA.pos Λ
  unfold energyDecayConst₂
  positivity

theorem excessDecayConst₂_nonneg {A₀ : Space d →L[ℝ] Space d} {ν Λ : ℝ}
    (hA : IsUniformlyElliptic A₀ ν Λ) : 0 ≤ excessDecayConst₂ d ν Λ := by
  have := aHarmonicGradExcessConst_nonneg' hA
  have := comparisonConst_nonneg d hA.pos Λ
  unfold excessDecayConst₂
  positivity

/-- **Energy decay at a center** for Hölder continuous coefficients. -/
theorem variable_energy_decay (hd : 0 < d) {a : Space d → Space d →L[ℝ] Space d}
    {G : Space d → Space d} {w : Space d → ℝ} {K : NNReal} (hw : LipschitzWith K w)
    {x₀ : Space d} {R ν Λ H HG α : ℝ} (hα0 : 0 < α) (hν : 0 < ν) (hH : 0 ≤ H) (hHG : 0 ≤ HG)
    (hsymm : ∀ y ∈ ball x₀ R, ∀ u v, inner ℝ (a y u) v = inner ℝ u (a y v))
    (hell : ∀ y ∈ ball x₀ R, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a y ξ) ξ)
    (hbd : ∀ y ∈ ball x₀ R, ‖a y‖ ≤ Λ)
    (ha_hol : ∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R, ‖a y - a y'‖ ≤ H * dist y y' ^ α)
    (hG_hol : ∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R, ‖G y - G y'‖ ≤ HG * dist y y' ^ α)
    (heq : IsWeakDivFree (fun y ↦ a y (gradient w y) - G y) (ball x₀ R))
    {x : Space d} {s : ℝ} (hxs : closedBall x s ⊆ ball x₀ R) (hs : 0 < s) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρs : ρ ≤ s) :
    ∫ y in ball x ρ, ‖fderiv ℝ w y‖ ^ 2 ≤
      energyDecayConst₁ d ν Λ * (ρ / s) ^ d * (∫ y in ball x s, ‖fderiv ℝ w y‖ ^ 2) +
        energyDecayConst₂ d ν Λ * (2 * H ^ 2 * s ^ (2 * α) *
          (∫ y in ball x s, ‖fderiv ℝ w y‖ ^ 2) +
          2 * HG ^ 2 * volume.real (ball (0 : Space d) 1) * s ^ ((d : ℝ) + 2 * α)) := by
  have hx0 : x ∈ ball x₀ R := hxs (mem_closedBall_self hs.le)
  have ha_cont := continuousOn_of_holder hα0 ha_hol
  have hG_cont := continuousOn_of_holder hα0 hG_hol
  have hAx := isUniformlyElliptic_of_bounds hd hν (hsymm x hx0) (hell x hx0) (hbd x hx0)
  obtain ⟨hFm, hFb⟩ := frozen_rhs_bound hw hα0 hH hHG ha_cont hG_cont ha_hol hG_hol hxs hs
  have hFeq := frozen_weakDivFree hw ha_cont hG_cont hbd heq hxs
  have hdec := energy_decay_of_weakDivFree hd hAx (hbd x hx0) hs hFm hw hFeq hρ0 hρs
  have hC₄ := energyDecayConst₂_nonneg hAx
  exact hdec.trans (by gcongr)

/-- **Excess decay at a center** for Hölder continuous coefficients. -/
theorem variable_excess_decay (hd : 0 < d) {a : Space d → Space d →L[ℝ] Space d}
    {G : Space d → Space d} {w : Space d → ℝ} {K : NNReal} (hw : LipschitzWith K w)
    {x₀ : Space d} {R ν Λ H HG α : ℝ} (hα0 : 0 < α) (hν : 0 < ν) (hH : 0 ≤ H) (hHG : 0 ≤ HG)
    (hsymm : ∀ y ∈ ball x₀ R, ∀ u v, inner ℝ (a y u) v = inner ℝ u (a y v))
    (hell : ∀ y ∈ ball x₀ R, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a y ξ) ξ)
    (hbd : ∀ y ∈ ball x₀ R, ‖a y‖ ≤ Λ)
    (ha_hol : ∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R, ‖a y - a y'‖ ≤ H * dist y y' ^ α)
    (hG_hol : ∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R, ‖G y - G y'‖ ≤ HG * dist y y' ^ α)
    (heq : IsWeakDivFree (fun y ↦ a y (gradient w y) - G y) (ball x₀ R))
    {x : Space d} {s : ℝ} (hxs : closedBall x s ⊆ ball x₀ R) (hs : 0 < s) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    ∫ y in ball x (θ * s), ‖fderiv ℝ w y - ⨍ z in ball x (θ * s), fderiv ℝ w z‖ ^ 2 ≤
      excessDecayConst₁ d ν Λ * θ ^ (d + 2) *
          (∫ y in ball x s, ‖fderiv ℝ w y - ⨍ z in ball x s, fderiv ℝ w z‖ ^ 2) +
        excessDecayConst₂ d ν Λ * (2 * H ^ 2 * s ^ (2 * α) *
          (∫ y in ball x s, ‖fderiv ℝ w y‖ ^ 2) +
          2 * HG ^ 2 * volume.real (ball (0 : Space d) 1) * s ^ ((d : ℝ) + 2 * α)) := by
  have hx0 : x ∈ ball x₀ R := hxs (mem_closedBall_self hs.le)
  have ha_cont := continuousOn_of_holder hα0 ha_hol
  have hG_cont := continuousOn_of_holder hα0 hG_hol
  have hAx := isUniformlyElliptic_of_bounds hd hν (hsymm x hx0) (hell x hx0) (hbd x hx0)
  obtain ⟨hFm, hFb⟩ := frozen_rhs_bound hw hα0 hH hHG ha_cont hG_cont ha_hol hG_hol hxs hs
  have hFeq := frozen_weakDivFree hw ha_cont hG_cont hbd heq hxs
  have hdec := excess_decay_of_weakDivFree hd hAx (hbd x hx0) hs hFm hw hFeq hθ0 hθ
  have hC₂ := excessDecayConst₂_nonneg hAx
  exact hdec.trans (by gcongr)

/-- **Schauder (Campanato) estimate for Hölder coefficients.** There are constants `C ≥ 0` and
`r₀ ∈ (0, R/2]`, depending only on `d, α, ν, Λ, H, R`, such that every Lipschitz weak solution
`w` of `div (a ∇w) = div G` in `B_R(x₀)`, with `a` symmetric, `ν`-elliptic, bounded by `Λ` and
`α`-Hölder with constant `H`, and `G` `α`-Hölder with constant `HG`, satisfies
`∫_{B_r(x)} ‖Dw - (Dw)_{B_r(x)}‖² ≤ C (∫_{B_R(x₀)} ‖Dw‖² + HG²) r^(d + α/2)`
for all `x ∈ B_{R/2}(x₀)` and `0 < r ≤ r₀`. -/
theorem schauder_excess_estimate (hd : 0 < d) {α ν Λ H R : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hν : 0 < ν) (hνΛ : ν ≤ Λ) (hR : 0 < R) (hH : 0 ≤ H) :
    ∃ C r₀ : ℝ, 0 ≤ C ∧ 0 < r₀ ∧ r₀ ≤ R / 2 ∧
      ∀ (x₀ : Space d) (a : Space d → Space d →L[ℝ] Space d) (G : Space d → Space d) (HG : ℝ)
        (w : Space d → ℝ) (K : NNReal),
        (∀ y ∈ ball x₀ R, ∀ u v, inner ℝ (a y u) v = inner ℝ u (a y v)) →
        (∀ y ∈ ball x₀ R, ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (a y ξ) ξ) →
        (∀ y ∈ ball x₀ R, ‖a y‖ ≤ Λ) →
        (∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R, ‖a y - a y'‖ ≤ H * dist y y' ^ α) →
        0 ≤ HG →
        (∀ y ∈ ball x₀ R, ∀ y' ∈ ball x₀ R, ‖G y - G y'‖ ≤ HG * dist y y' ^ α) →
        LipschitzWith K w →
        IsWeakDivFree (fun y ↦ a y (gradient w y) - G y) (ball x₀ R) →
        ∀ x ∈ ball x₀ (R / 2), ∀ r, 0 < r → r ≤ r₀ →
          ∫ y in ball x r, ‖fderiv ℝ w y - ⨍ z in ball x r, fderiv ℝ w z‖ ^ 2 ≤
            C * ((∫ y in ball x₀ R, ‖fderiv ℝ w y‖ ^ 2) + HG ^ 2) * r ^ ((d : ℝ) + α / 2) := by
  have hA0 := isUniformlyElliptic_smul_id hd hν hνΛ
  have hCe0 := aHarmonicGradExcessConst_nonneg' hA0
  have hC₁0 : 0 ≤ excessDecayConst₁ d ν Λ := by unfold excessDecayConst₁; positivity
  have hC₂0 := excessDecayConst₂_nonneg hA0
  have hC₃1 : 1 ≤ energyDecayConst₁ d ν Λ := by
    unfold energyDecayConst₁
    have h1 : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
    have h2 : 0 ≤ 4 * (2 * aHarmonicGradExcessConst d ν Λ + 2) * 8 ^ d := by positivity
    linarith
  have hC₄0 := energyDecayConst₂_nonneg hA0
  obtain ⟨KM, r₁, hKM0, hr₁0, hr₁R, hMorrey⟩ :=
    morrey_iteration hd hα0 hα1 hC₃1 hC₄0 (H := H) (half_pos hR)
  obtain ⟨KC, θC, hKC0, hθC0, hθC14, hCamp⟩ := campanato_iteration (d := d) hα0 hα1 hC₁0
  obtain ⟨ωd, hωd⟩ : ∃ c, c = volume.real (ball (0 : Space d) 1) := ⟨_, rfl⟩
  have hωd0 : 0 < ωd := hωd ▸ measureReal_unitBall_pos
  obtain ⟨C₂, hC₂⟩ : ∃ c, c = excessDecayConst₂ d ν Λ := ⟨_, rfl⟩
  obtain ⟨C₄, hC₄⟩ : ∃ c, c = energyDecayConst₂ d ν Λ := ⟨_, rfl⟩
  rw [← hC₂] at hC₂0
  rw [← hC₄] at hC₄0 hMorrey
  obtain ⟨P, hP⟩ : ∃ p : ℝ, p = 2 * H ^ 2 * KM * r₁ ^ (-((d : ℝ) - α)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ q : ℝ,
      q = P * (C₄ * 2 * ωd * r₁ ^ ((d : ℝ) + 2 * α)) + 2 * ωd * r₁ ^ α := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hP]
    have := Real.rpow_nonneg hr₁0.le (-((d : ℝ) - α))
    positivity
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    have := Real.rpow_nonneg hr₁0.le ((d : ℝ) + 2 * α)
    have := Real.rpow_nonneg hr₁0.le α
    positivity
  have hr₁σ : 0 ≤ r₁ ^ (-((d : ℝ) + α / 2)) := Real.rpow_nonneg hr₁0.le _
  have hr₁τ : 0 ≤ r₁ ^ ((d : ℝ) + α) := Real.rpow_nonneg hr₁0.le _
  refine ⟨KC * r₁ ^ (-((d : ℝ) + α / 2)) * (4 + C₂ * r₁ ^ ((d : ℝ) + α) * (P + Q)), r₁,
    by positivity, hr₁0, hr₁R, ?_⟩
  intro x₀ a G HG w K hsymm hell hbd ha_hol hHG hG_hol hw heq x hx r hr hrr₁
  have hxr : ∀ s, s ≤ R / 2 → closedBall x s ⊆ ball x₀ R := by
    intro s hs z hz
    rw [mem_closedBall] at hz
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle z x x₀]
  obtain ⟨W, hW⟩ : ∃ W, W = ∫ y in ball x₀ R, ‖fderiv ℝ w y‖ ^ 2 := ⟨_, rfl⟩
  have hiD : ∀ (c : Space d) (s : ℝ), IntegrableOn (fun y ↦ ‖fderiv ℝ w y‖ ^ 2) (ball c s) :=
    fun c s ↦ integrableOn_norm_sq_of_le measure_ball_lt_top.ne measurableSet_ball
      (measurable_fderiv ℝ w).aestronglyMeasurable (fun y _ ↦ norm_fderiv_le_of_lipschitz ℝ hw)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℝ, Φ = fun s ↦ ∫ y in ball x s, ‖fderiv ℝ w y‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → ℝ, Ψ = fun s ↦
      ∫ y in ball x s, ‖fderiv ℝ w y - ⨍ z in ball x s, fderiv ℝ w z‖ ^ 2 := ⟨_, rfl⟩
  have hΦ0 : ∀ s, 0 ≤ Φ s := fun s ↦ by rw [hΦ]; exact integral_nonneg fun _ ↦ sq_nonneg _
  have hΨ0 : ∀ s, 0 ≤ Ψ s := fun s ↦ by rw [hΨ]; exact integral_nonneg fun _ ↦ sq_nonneg _
  have hΦmono : ∀ s t, s ≤ t → Φ s ≤ Φ t := fun s t hst ↦ by
    rw [hΦ]
    exact setIntegral_mono_set (hiD x t) (Eventually.of_forall fun y ↦ sq_nonneg _)
      (ball_subset_ball hst).eventuallyLE
  have hΦW : Φ r₁ ≤ W := by
    rw [hΦ, hW]
    exact setIntegral_mono_set (hiD x₀ R) (Eventually.of_forall fun y ↦ sq_nonneg _)
      (ball_subset_closedBall.trans (hxr r₁ hr₁R)).eventuallyLE
  have hW0 : 0 ≤ W := (hΦ0 r₁).trans hΦW
  have hΨmono : ∀ s t, 0 < s → s ≤ t → Ψ s ≤ 4 * Ψ t := by
    intro s t _ hst
    rw [hΨ]
    have : IsFiniteMeasure (volume.restrict (ball x t)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have h1 := setIntegral_norm_sub_setAverage_sq_le (measure_ball_lt_top (x := x) (r := s)).ne
      (memLp_fderiv_of_lipschitz hw _ measure_ball_lt_top.ne) (⨍ z in ball x t, fderiv ℝ w z)
    have hit : IntegrableOn (fun y ↦ ‖fderiv ℝ w y - ⨍ z in ball x t, fderiv ℝ w z‖ ^ 2)
        (ball x t) :=
      ((memLp_fderiv_of_lipschitz hw _ measure_ball_lt_top.ne).sub
        (memLp_const _)).norm.integrable_sq
    have h2 : ∫ y in ball x s, ‖fderiv ℝ w y - ⨍ z in ball x t, fderiv ℝ w z‖ ^ 2 ≤
        ∫ y in ball x t, ‖fderiv ℝ w y - ⨍ z in ball x t, fderiv ℝ w z‖ ^ 2 :=
      setIntegral_mono_set hit (Eventually.of_forall fun y ↦ sq_nonneg _)
        (ball_subset_ball hst).eventuallyLE
    simp only
    linarith only [h1, h2]
  have hΨΦ : Ψ r₁ ≤ 4 * W := by
    have h1 := setIntegral_norm_sub_setAverage_sq_le (measure_ball_lt_top (x := x) (r := r₁)).ne
      (memLp_fderiv_of_lipschitz hw _ measure_ball_lt_top.ne) 0
    simp only [sub_zero] at h1
    have h2 : Ψ r₁ ≤ 4 * Φ r₁ := by rw [hΨ, hΦ]; exact h1
    linarith only [h2, hΦW]
  -- the Morrey bound
  have hdecΦ : ∀ ρ s, 0 < ρ → ρ ≤ s → s ≤ R / 2 → Φ ρ ≤ energyDecayConst₁ d ν Λ *
      (ρ / s) ^ d * Φ s + C₄ * (2 * H ^ 2 * s ^ (2 * α) * Φ s +
        (2 * HG ^ 2 * ωd) * s ^ ((d : ℝ) + 2 * α)) := by
    intro ρ s hρ hρs hsR
    have hs : 0 < s := hρ.trans_le hρs
    have h := variable_energy_decay hd hw hα0 hν hH hHG hsymm hell hbd ha_hol hG_hol heq
      (hxr s hsR) hs hρ hρs
    rw [← hC₄, ← hωd] at h
    rw [hΦ]
    convert h using 3
  have hΦb := hMorrey Φ (2 * HG ^ 2 * ωd) (by positivity) hΦ0 hΦmono hdecΦ
  -- the Campanato bound
  obtain ⟨BC, hBC⟩ : ∃ b : ℝ, b = 2 * H ^ 2 * KM * r₁ ^ (-((d : ℝ) - α)) *
      (Φ r₁ + C₄ * (2 * HG ^ 2 * ωd) * r₁ ^ ((d : ℝ) + 2 * α)) + 2 * HG ^ 2 * ωd * r₁ ^ α :=
    ⟨_, rfl⟩
  have hBC0 : 0 ≤ BC := by
    rw [hBC]
    have := Real.rpow_nonneg hr₁0.le (-((d : ℝ) - α))
    have := Real.rpow_nonneg hr₁0.le ((d : ℝ) + 2 * α)
    have := Real.rpow_nonneg hr₁0.le α
    have := hΦ0 r₁
    positivity
  have hRHS : ∀ s, 0 < s → s ≤ r₁ → 2 * H ^ 2 * s ^ (2 * α) * Φ s +
      2 * HG ^ 2 * ωd * s ^ ((d : ℝ) + 2 * α) ≤ BC * s ^ ((d : ℝ) + α) := by
    intro s hs hsr
    have hΦs := hΦb s hs hsr
    have e1 : s ^ (2 * α) * (s / r₁) ^ ((d : ℝ) - α) =
        s ^ ((d : ℝ) + α) * r₁ ^ (-((d : ℝ) - α)) := by
      rw [Real.div_rpow hs.le hr₁0.le, Real.rpow_neg hr₁0.le, div_eq_mul_inv, ← mul_assoc,
        ← Real.rpow_add hs, show 2 * α + ((d : ℝ) - α) = (d : ℝ) + α by ring]
    have e2 : s ^ ((d : ℝ) + 2 * α) = s ^ ((d : ℝ) + α) * s ^ α := by
      rw [← Real.rpow_add hs, show (d : ℝ) + α + α = (d : ℝ) + 2 * α by ring]
    have e3 : s ^ α ≤ r₁ ^ α := Real.rpow_le_rpow hs.le hsr hα0.le
    have hs2α : 0 ≤ s ^ (2 * α) := Real.rpow_nonneg hs.le _
    have hsτ : 0 ≤ s ^ ((d : ℝ) + α) := Real.rpow_nonneg hs.le _
    calc 2 * H ^ 2 * s ^ (2 * α) * Φ s + 2 * HG ^ 2 * ωd * s ^ ((d : ℝ) + 2 * α) ≤
        2 * H ^ 2 * s ^ (2 * α) * (KM * (s / r₁) ^ ((d : ℝ) - α) *
          (Φ r₁ + C₄ * (2 * HG ^ 2 * ωd) * r₁ ^ ((d : ℝ) + 2 * α))) +
        2 * HG ^ 2 * ωd * (s ^ ((d : ℝ) + α) * r₁ ^ α) := by
          rw [e2]
          gcongr
      _ = 2 * H ^ 2 * KM * (s ^ (2 * α) * (s / r₁) ^ ((d : ℝ) - α)) *
          (Φ r₁ + C₄ * (2 * HG ^ 2 * ωd) * r₁ ^ ((d : ℝ) + 2 * α)) +
          2 * HG ^ 2 * ωd * (s ^ ((d : ℝ) + α) * r₁ ^ α) := by ring
      _ = BC * s ^ ((d : ℝ) + α) := by
          rw [e1, hBC]
          ring
  have hdecΨ : ∀ s, 0 < s → s ≤ r₁ → Ψ (θC * s) ≤ excessDecayConst₁ d ν Λ * θC ^ (d + 2) *
      Ψ s + (C₂ * BC) * s ^ ((d : ℝ) + α) := by
    intro s hs hsr
    have h := variable_excess_decay hd hw hα0 hν hH hHG hsymm hell hbd ha_hol hG_hol heq
      (hxr s (hsr.trans hr₁R)) hs hθC0 hθC14
    rw [← hC₂, ← hωd] at h
    have h2 := hRHS s hs hsr
    have h3 : C₂ * (2 * H ^ 2 * s ^ (2 * α) * Φ s + 2 * HG ^ 2 * ωd * s ^ ((d : ℝ) + 2 * α)) ≤
        C₂ * (BC * s ^ ((d : ℝ) + α)) := mul_le_mul_of_nonneg_left h2 hC₂0
    have h4 : Ψ (θC * s) ≤ excessDecayConst₁ d ν Λ * θC ^ (d + 2) * Ψ s +
        C₂ * (2 * H ^ 2 * s ^ (2 * α) * Φ s + 2 * HG ^ 2 * ωd * s ^ ((d : ℝ) + 2 * α)) := by
      rw [hΨ, hΦ]
      exact h
    linarith only [h3, h4]
  have hΨb := hCamp Ψ (C₂ * BC) r₁ (mul_nonneg hC₂0 hBC0) hr₁0 hΨ0 hΨmono hdecΨ r hr hrr₁
  -- conclusion
  have hBCle : BC ≤ P * W + Q * HG ^ 2 := by
    have e : BC = P * Φ r₁ + Q * HG ^ 2 := by rw [hBC, hQ, hP]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hΦW hP0
    linarith only [this]
  have hrr : (r / r₁) ^ ((d : ℝ) + α / 2) = r ^ ((d : ℝ) + α / 2) * r₁ ^ (-((d : ℝ) + α / 2)) := by
    rw [Real.div_rpow hr.le hr₁0.le, Real.rpow_neg hr₁0.le, div_eq_mul_inv]
  have hrσ : 0 ≤ r ^ ((d : ℝ) + α / 2) := Real.rpow_nonneg hr.le _
  have hHG2 : 0 ≤ HG ^ 2 := sq_nonneg HG
  have hfinal : Ψ r₁ + C₂ * BC * r₁ ^ ((d : ℝ) + α) ≤
      (4 + C₂ * r₁ ^ ((d : ℝ) + α) * (P + Q)) * (W + HG ^ 2) := by
    have h1 : C₂ * BC * r₁ ^ ((d : ℝ) + α) ≤ C₂ * (P * W + Q * HG ^ 2) * r₁ ^ ((d : ℝ) + α) := by
      gcongr
    have h2 : 0 ≤ C₂ * r₁ ^ ((d : ℝ) + α) * (P * HG ^ 2 + Q * W) := by positivity
    have e : (4 + C₂ * r₁ ^ ((d : ℝ) + α) * (P + Q)) * (W + HG ^ 2) = 4 * W + 4 * HG ^ 2 +
        C₂ * (P * W + Q * HG ^ 2) * r₁ ^ ((d : ℝ) + α) +
          C₂ * r₁ ^ ((d : ℝ) + α) * (P * HG ^ 2 + Q * W) := by ring
    rw [e]
    linarith only [h1, h2, hΨΦ, hHG2]
  calc ∫ y in ball x r, ‖fderiv ℝ w y - ⨍ z in ball x r, fderiv ℝ w z‖ ^ 2 = Ψ r := by rw [hΨ]
    _ ≤ KC * (r / r₁) ^ ((d : ℝ) + α / 2) * (Ψ r₁ + C₂ * BC * r₁ ^ ((d : ℝ) + α)) := hΨb
    _ ≤ KC * (r / r₁) ^ ((d : ℝ) + α / 2) *
        ((4 + C₂ * r₁ ^ ((d : ℝ) + α) * (P + Q)) * (W + HG ^ 2)) := by gcongr
    _ = KC * r₁ ^ (-((d : ℝ) + α / 2)) * (4 + C₂ * r₁ ^ ((d : ℝ) + α) * (P + Q)) *
        (W + HG ^ 2) * r ^ ((d : ℝ) + α / 2) := by
        rw [hrr]
        ring
    _ = KC * r₁ ^ (-((d : ℝ) + α / 2)) * (4 + C₂ * r₁ ^ ((d : ℝ) + α) * (P + Q)) *
        ((∫ y in ball x₀ R, ‖fderiv ℝ w y‖ ^ 2) + HG ^ 2) * r ^ ((d : ℝ) + α / 2) := by
        rw [hW]

end SerrinEpigraph
