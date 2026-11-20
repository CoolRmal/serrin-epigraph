module

public import SerrinEpigraph.FlatGraph
public import SerrinEpigraph.DifferenceQuotientRegularity
public import SerrinEpigraph.SmoothBoundaryChart
public import SerrinEpigraph.BoundaryChartGluing

/-!
# Graph charts of `C¹` boundary points of perimeter minimizers

* `exists_C1_graph_of_fderiv_last_pos`: the implicit function theorem in graph form — a `C¹`
  function `G` with `G 0 = 0`, `∂_n G(0) > 0` and vanishing horizontal derivative at `0` has
  `{G > 0} = {t > φ(y)}` near `0` for a `C¹` function `φ` with `φ 0 = 0`, `Dφ(0) = 0`.
* `IsC1BoundaryPoint.exists_graphChart`: at a `C¹` boundary point `x` of `E`, in the frame
  `z ↦ Q z + x` with `Q e_n` the inner unit normal, `E` is a.e. the supergraph of such a `φ` on a
  cylinder.
* `IsLocalPerimeterMinimizer.isWeakSolution_minimalSurfaceFlux_of_graph`: if a local perimeter
  minimizer in the whole space is a.e. the supergraph of a `C¹` function `φ` on a cylinder, then
  `φ` is a weak solution of the minimal surface equation (first variation of the graph area,
  computed with `graph_perimeter_eq_area`).
* `IsLocalPerimeterMinimizer.exists_minimalGraphChart`: both together.
* `isSmoothBoundaryChart_of_graphChart`: a smooth graph chart is an `IsSmoothBoundaryChart`.
* `c1RegularSmoothHyp_of_minimalSurface`: `C1RegularSmoothHyp` follows from the smoothness of `C¹`
  weak solutions of the minimal surface equation on balls.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal NNReal ContDiff

namespace SerrinEpigraph

theorem point_eq_point_zero_add {m : ℕ} (y : Space m) (t : ℝ) :
    point y t = point y 0 + t • verticalDirection m := by
  rw [point_add_vertical, zero_add]

theorem hasDerivAt_point_last {m : ℕ} (y : Space m) (t : ℝ) :
    HasDerivAt (point y) (verticalDirection m) t := by
  simpa only [point_add_vertical, zero_add, id_eq, one_smul] using
    ((hasDerivAt_id t).smul_const (verticalDirection m)).const_add (point y 0)

/-- **The implicit function theorem in graph form.** -/
theorem exists_C1_graph_of_fderiv_last_pos {m : ℕ} {G : Space (m + 1) → ℝ} {r : ℝ}
    (hr : 0 < r) (hG : ContDiffOn ℝ 1 G (ball 0 r)) (hG0 : G 0 = 0)
    (hGn : 0 < fderiv ℝ G 0 (verticalDirection m))
    (hGh : ∀ v : Space m, fderiv ℝ G 0 (point v 0) = 0) :
    ∃ (φ : Space m → ℝ) (ρ h : ℝ), 0 < ρ ∧ 0 < h ∧
      cylinderSet (ball (0 : Space m) ρ) h ⊆ ball (0 : Space (m + 1)) r ∧
      ContDiffOn ℝ 1 φ (ball 0 ρ) ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      (∀ y ∈ ball (0 : Space m) ρ, |φ y| < h) ∧
      ∀ z ∈ cylinderSet (ball (0 : Space m) ρ) h,
        (0 < G z ↔ φ (horizontal z) < z (Fin.last m)) := by
  set c := fderiv ℝ G 0 (verticalDirection m) with hc_def
  have hDGc : ContinuousOn (fderiv ℝ G) (ball 0 r) :=
    hG.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hGd : ∀ z ∈ ball (0 : Space (m + 1)) r, HasFDerivAt G (fderiv ℝ G z) z := fun z hz ↦
    (((hG.differentiableOn one_ne_zero) z hz).differentiableAt
      (isOpen_ball.mem_nhds hz)).hasFDerivAt
  -- a closed ball on which `DG` is close to `DG 0`
  obtain ⟨s, hs, hsr, hsDG⟩ : ∃ s > 0, closedBall (0 : Space (m + 1)) s ⊆ ball 0 r ∧
      ∀ z ∈ closedBall (0 : Space (m + 1)) s, ‖fderiv ℝ G z - fderiv ℝ G 0‖ ≤ c / 2 := by
    have hca := (hDGc 0 (mem_ball_self hr)).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    rw [Metric.continuousAt_iff] at hca
    obtain ⟨δ, hδ, hδf⟩ := hca (c / 2) (by positivity)
    refine ⟨min (δ / 2) (r / 2), by positivity,
      closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith)),
      fun z hz ↦ ?_⟩
    have hz' : dist z 0 < δ := lt_of_le_of_lt (mem_closedBall.mp hz)
      (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have := hδf hz'
    rw [dist_eq_norm] at this
    exact this.le
  set M := ‖fderiv ℝ G 0‖ + c / 2 with hM_def
  have hM : ∀ z ∈ closedBall (0 : Space (m + 1)) s, ‖fderiv ℝ G z‖ ≤ M := by
    intro z hz
    have := norm_le_insert' (fderiv ℝ G z) (fderiv ℝ G 0)
    linarith [hsDG z hz]
  have hcz : ∀ z ∈ closedBall (0 : Space (m + 1)) s, c / 2 ≤ fderiv ℝ G z (verticalDirection m) := by
    intro z hz
    have h1 : fderiv ℝ G z (verticalDirection m) =
        c + (fderiv ℝ G z - fderiv ℝ G 0) (verticalDirection m) := by
      simp [hc_def]
    have h2 := ((fderiv ℝ G z - fderiv ℝ G 0).le_opNorm (verticalDirection m))
    rw [norm_verticalDirection, mul_one] at h2
    have h3 := (abs_le.mp ((Real.norm_eq_abs _).symm ▸ h2.trans (hsDG z hz))).1
    linarith
  have hc0 : 0 < c := hGn
  have hM0 : 0 < M := by
    have := norm_nonneg (fderiv ℝ G 0)
    linarith
  set h := s / 2 with hh_def
  have hh : 0 < h := by positivity
  have hcyl_s : ∀ y : Space m, ‖y‖ ≤ h → ∀ t ∈ Icc (-h) h, point y t ∈ closedBall 0 s := by
    intro y hy t ht
    rw [mem_closedBall, dist_zero_right]
    have := norm_le_norm_horizontal_add_abs_last (point y t)
    rw [horizontal_point, last_point] at this
    have ht' : |t| ≤ h := abs_le.mpr ⟨ht.1, ht.2⟩
    linarith
  -- monotonicity along vertical segments
  have hmono : ∀ y : Space m, ‖y‖ ≤ h → ∀ t₁ ∈ Icc (-h) h, ∀ t₂ ∈ Icc (-h) h, t₁ ≤ t₂ →
      c / 2 * (t₂ - t₁) ≤ G (point y t₂) - G (point y t₁) := by
    intro y hy t₁ ht₁ t₂ ht₂ ht
    have hcont : ContinuousOn (fun t ↦ G (point y t)) (Icc (-h) h) := by
      refine (hG.continuousOn.comp (continuous_point y).continuousOn) fun t ht ↦ ?_
      exact hsr (hcyl_s y hy t ht)
    have hderiv : ∀ t ∈ Icc (-h) h, HasDerivAt (fun t ↦ G (point y t))
        (fderiv ℝ G (point y t) (verticalDirection m)) t := fun t ht ↦
      (hGd _ (hsr (hcyl_s y hy t ht))).comp_hasDerivAt t (hasDerivAt_point_last y t)
    have hdiff : DifferentiableOn ℝ (fun t ↦ G (point y t)) (interior (Icc (-h) h)) :=
      fun t ht ↦ (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    have hle : ∀ t ∈ interior (Icc (-h) h), c / 2 ≤ deriv (fun t ↦ G (point y t)) t := by
      intro t ht
      rw [(hderiv t (interior_subset ht)).deriv]
      exact hcz _ (hcyl_s y hy t (interior_subset ht))
    exact (convex_Icc (-h) h).mul_sub_le_image_sub_of_le_deriv hcont hdiff hle t₁ ht₁ t₂ ht₂ ht
  -- horizontal Lipschitz bound
  have hhor : ∀ y₁ y₂ : Space m, ‖y₁‖ ≤ h → ‖y₂‖ ≤ h → ∀ t ∈ Icc (-h) h,
      |G (point y₁ t) - G (point y₂ t)| ≤ M * ‖y₁ - y₂‖ := by
    intro y₁ y₂ hy₁ hy₂ t ht
    have hmv := (convex_closedBall (0 : Space (m + 1)) s).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ (hGd z (hsr hz)).differentiableAt) hM (hcyl_s y₂ hy₂ t ht)
      (hcyl_s y₁ hy₁ t ht)
    rw [Real.norm_eq_abs, point_sub_point, sub_self, norm_point_zero] at hmv
    exact hmv
  -- the sign change
  set ρ := min h (c * h / (4 * M)) with hρ_def
  have hρ : 0 < ρ := lt_min hh (by positivity)
  have hρh : ρ ≤ h := min_le_left _ _
  have hρM : M * ρ ≤ c * h / 4 := by
    have := min_le_right h (c * h / (4 * M))
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hG0t : ∀ t ∈ Icc (-h) h, G (point 0 t) = G (point 0 t) := fun _ _ ↦ rfl
  have hpt00 : point (0 : Space m) 0 = 0 := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point]
  have hmemIcc : ∀ t, |t| < h → t ∈ Icc (-h) h := fun t ht ↦
    ⟨by linarith [(abs_lt.mp ht).1], by linarith [(abs_lt.mp ht).2]⟩
  have hhIcc : h ∈ Icc (-h) h := ⟨by linarith, le_rfl⟩
  have hmhIcc : -h ∈ Icc (-h) h := ⟨le_rfl, by linarith⟩
  have h0Icc : (0 : ℝ) ∈ Icc (-h) h := ⟨by linarith, by linarith⟩
  have htop : ∀ y ∈ ball (0 : Space m) ρ, 0 < G (point y h) := by
    intro y hy
    have hy' : ‖y‖ < ρ := mem_ball_zero_iff.mp hy
    have h1 := hmono 0 (by simp; linarith) 0 h0Icc h hhIcc hh.le
    rw [hpt00, hG0] at h1
    have h2 := hhor y 0 (by linarith) (by simp; linarith) h hhIcc
    rw [sub_zero] at h2
    have h3 := (abs_le.mp h2).1
    have h4 : M * ‖y‖ ≤ M * ρ := mul_le_mul_of_nonneg_left hy'.le hM0.le
    nlinarith
  have hbot : ∀ y ∈ ball (0 : Space m) ρ, G (point y (-h)) < 0 := by
    intro y hy
    have hy' : ‖y‖ < ρ := mem_ball_zero_iff.mp hy
    have h1 := hmono 0 (by simp; linarith) (-h) hmhIcc 0 h0Icc (by linarith)
    rw [hpt00, hG0] at h1
    have h2 := hhor y 0 (by linarith) (by simp; linarith) (-h) hmhIcc
    rw [sub_zero] at h2
    have h3 := (abs_le.mp h2).2
    have h4 : M * ‖y‖ ≤ M * ρ := mul_le_mul_of_nonneg_left hy'.le hM0.le
    nlinarith
  -- the implicit function
  have hex : ∀ y, ∃ t, y ∈ ball (0 : Space m) ρ → t ∈ Ioo (-h) h ∧ G (point y t) = 0 := by
    intro y
    by_cases hy : y ∈ ball (0 : Space m) ρ
    · have hy' : ‖y‖ ≤ h := (mem_ball_zero_iff.mp hy).le.trans hρh
      have hcont : ContinuousOn (fun t ↦ G (point y t)) (Icc (-h) h) := by
        refine (hG.continuousOn.comp (continuous_point y).continuousOn) fun t ht ↦ ?_
        exact hsr (hcyl_s y hy' t ht)
      have hivt := intermediate_value_Ioo (by linarith) hcont
      obtain ⟨t, ht, ht0⟩ := hivt ⟨hbot y hy, htop y hy⟩
      exact ⟨t, fun _ ↦ ⟨ht, ht0⟩⟩
    · exact ⟨0, fun h' ↦ absurd h' hy⟩
  choose φ hφ using hex
  have hφI : ∀ y ∈ ball (0 : Space m) ρ, φ y ∈ Ioo (-h) h := fun y hy ↦ (hφ y hy).1
  have hφ0' : ∀ y ∈ ball (0 : Space m) ρ, G (point y (φ y)) = 0 := fun y hy ↦ (hφ y hy).2
  have hyh : ∀ y ∈ ball (0 : Space m) ρ, ‖y‖ ≤ h := fun y hy ↦
    (mem_ball_zero_iff.mp hy).le.trans hρh
  have hφIcc : ∀ y ∈ ball (0 : Space m) ρ, φ y ∈ Icc (-h) h := fun y hy ↦
    ⟨(hφI y hy).1.le, (hφI y hy).2.le⟩
  -- the sign of `G` on the cylinder
  have hsign : ∀ y ∈ ball (0 : Space m) ρ, ∀ t ∈ Icc (-h) h,
      (0 < G (point y t) ↔ φ y < t) := by
    intro y hy t ht
    constructor
    · intro hpos
      by_contra hle
      push Not at hle
      have := hmono y (hyh y hy) t ht (φ y) (hφIcc y hy) hle
      rw [hφ0' y hy] at this
      nlinarith
    · intro hlt
      have := hmono y (hyh y hy) (φ y) (hφIcc y hy) t ht hlt.le
      rw [hφ0' y hy] at this
      nlinarith
  have hzero : ∀ y ∈ ball (0 : Space m) ρ, ∀ t ∈ Icc (-h) h, G (point y t) = 0 → t = φ y := by
    intro y hy t ht h0
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hmono y (hyh y hy) t ht (φ y) (hφIcc y hy) hlt.le
      rw [hφ0' y hy, h0] at this
      nlinarith
    · have := (hsign y hy t ht).mpr hgt
      linarith
  have hφ00 : φ 0 = 0 := by
    have h0b : (0 : Space m) ∈ ball (0 : Space m) ρ := mem_ball_self hρ
    exact (hzero 0 h0b 0 h0Icc (by rw [hpt00, hG0])).symm
  -- Lipschitz continuity of `φ`
  have hlip : ∀ y₁ ∈ ball (0 : Space m) ρ, ∀ y₂ ∈ ball (0 : Space m) ρ,
      |φ y₁ - φ y₂| ≤ 2 * M / c * ‖y₁ - y₂‖ := by
    intro y₁ hy₁ y₂ hy₂
    have hA : c / 2 * |φ y₁ - φ y₂| ≤ |G (point y₁ (φ y₁)) - G (point y₁ (φ y₂))| := by
      rcases le_total (φ y₂) (φ y₁) with h12 | h12
      · have := hmono y₁ (hyh y₁ hy₁) (φ y₂) (hφIcc y₂ hy₂) (φ y₁) (hφIcc y₁ hy₁) h12
        rw [abs_of_nonneg (by linarith : 0 ≤ φ y₁ - φ y₂)]
        exact this.trans (le_abs_self _)
      · have := hmono y₁ (hyh y₁ hy₁) (φ y₁) (hφIcc y₁ hy₁) (φ y₂) (hφIcc y₂ hy₂) h12
        rw [abs_of_nonpos (by linarith : φ y₁ - φ y₂ ≤ 0), abs_sub_comm]
        calc c / 2 * -(φ y₁ - φ y₂) = c / 2 * (φ y₂ - φ y₁) := by ring
          _ ≤ G (point y₁ (φ y₂)) - G (point y₁ (φ y₁)) := this
          _ ≤ |G (point y₁ (φ y₂)) - G (point y₁ (φ y₁))| := le_abs_self _
    have hB : |G (point y₁ (φ y₁)) - G (point y₁ (φ y₂))| =
        |G (point y₂ (φ y₂)) - G (point y₁ (φ y₂))| := by
      rw [hφ0' y₁ hy₁, hφ0' y₂ hy₂]
    have hC := hhor y₂ y₁ (hyh y₂ hy₂) (hyh y₁ hy₁) (φ y₂) (hφIcc y₂ hy₂)
    rw [norm_sub_rev] at hC
    rw [hB] at hA
    have hA' := hA.trans hC
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    nlinarith [abs_nonneg (φ y₁ - φ y₂)]
  have hK0 : 0 ≤ 2 * M / c := by positivity
  have hφcont : ContinuousOn φ (ball 0 ρ) := by
    intro y₀ hy₀
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / (2 * M / c + 1), by positivity, fun y hy hyd ↦ ?_⟩
    rw [dist_eq_norm] at hyd
    rw [Real.dist_eq]
    have h1 := hlip y hy y₀ hy₀
    have h2 : 2 * M / c * ‖y - y₀‖ ≤ 2 * M / c * (ε / (2 * M / c + 1)) :=
      mul_le_mul_of_nonneg_left hyd.le hK0
    have h3 : 2 * M / c * (ε / (2 * M / c + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  -- graph points and the slope
  set P : Space m → Space (m + 1) := fun y ↦ point y (φ y) with hP_def
  have hPball : ∀ y ∈ ball (0 : Space m) ρ, P y ∈ ball (0 : Space (m + 1)) r := fun y hy ↦
    hsr (hcyl_s y (hyh y hy) (φ y) (hφIcc y hy))
  have hPcont : ContinuousOn P (ball 0 ρ) :=
    pointContinuousLinearMap.continuous.comp_continuousOn (continuousOn_id.prodMk hφcont)
  set a : Space m → ℝ := fun y ↦ fderiv ℝ G (P y) (verticalDirection m) with ha_def
  have ha : ∀ y ∈ ball (0 : Space m) ρ, c / 2 ≤ a y := fun y hy ↦
    hcz _ (hcyl_s y (hyh y hy) (φ y) (hφIcc y hy))
  set D : Space m → (Space m →L[ℝ] ℝ) := fun y ↦
    -(a y)⁻¹ • ((fderiv ℝ G (P y)).comp (horizontalEmbedding m)) with hD_def
  have hDapp : ∀ y w, D y w = -(a y)⁻¹ * fderiv ℝ G (P y) (point w 0) := by
    intro y w
    simp only [hD_def, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, horizontalEmbedding_apply, smul_eq_mul, neg_mul]
  have hderiv : ∀ y₀ ∈ ball (0 : Space m) ρ, HasFDerivAt φ (D y₀) y₀ := by
    intro y₀ hy₀
    have hGp := hGd _ (hPball y₀ hy₀)
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff] at hGp ⊢
    intro ε hε
    set K := 2 * M / c with hK
    set ε' := ε * (c / 2) / (1 + K) with hε'
    have hε'0 : 0 < ε' := by positivity
    have hGev := hGp hε'0
    have hball : ∀ᶠ w in 𝓝 (0 : Space m), y₀ + w ∈ ball (0 : Space m) ρ := by
      have hca : ContinuousAt (fun w : Space m ↦ y₀ + w) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have h2 : ball (0 : Space m) ρ ∈ 𝓝 (y₀ + 0) := by
        rw [add_zero]
        exact isOpen_ball.mem_nhds hy₀
      exact hca.preimage_mem_nhds h2
    have htend : Tendsto (fun w : Space m ↦ P (y₀ + w) - P y₀) (𝓝 0) (𝓝 0) := by
      have h1 : Tendsto (fun w : Space m ↦ y₀ + w) (𝓝 0) (𝓝 y₀) := by
        simpa using (continuous_const.add continuous_id).tendsto (0 : Space m) (f := fun w ↦ y₀ + w)
      have h2 := ((hPcont.continuousAt (isOpen_ball.mem_nhds hy₀)).tendsto).comp h1
      have h3 := h2.sub_const (P y₀)
      rw [sub_self] at h3
      exact h3
    filter_upwards [htend.eventually hGev, hball] with w hw hwb
    simp only [add_sub_cancel] at hw
    have hPw : P (y₀ + w) - P y₀ = point w (φ (y₀ + w) - φ y₀) := by
      rw [hP_def, point_sub_point, add_sub_cancel_left]
    have hlin : fderiv ℝ G (P y₀) (P (y₀ + w) - P y₀) =
        fderiv ℝ G (P y₀) (point w 0) + (φ (y₀ + w) - φ y₀) * a y₀ := by
      rw [hPw, point_eq_point_zero_add, map_add, map_smul, smul_eq_mul]
    have hG1 : G (P (y₀ + w)) = 0 := hφ0' _ hwb
    have hG2 : G (P y₀) = 0 := hφ0' _ hy₀
    rw [hG1, hG2, hlin] at hw
    have hΔ : |φ (y₀ + w) - φ y₀| ≤ K * ‖w‖ := by
      have := hlip (y₀ + w) hwb y₀ hy₀
      rwa [add_sub_cancel_left] at this
    have hnormP : ‖P (y₀ + w) - P y₀‖ ≤ (1 + K) * ‖w‖ := by
      rw [hPw]
      have := norm_le_norm_horizontal_add_abs_last (point w (φ (y₀ + w) - φ y₀))
      rw [horizontal_point, last_point] at this
      linarith
    have ha0 := ha y₀ hy₀
    have ha0' : 0 < a y₀ := by linarith
    rw [Real.norm_eq_abs] at hw ⊢
    rw [hDapp]
    have hkey : φ (y₀ + w) - φ y₀ - -(a y₀)⁻¹ * fderiv ℝ G (P y₀) (point w 0) =
        (a y₀)⁻¹ * -(0 - 0 - (fderiv ℝ G (P y₀) (point w 0) +
          (φ (y₀ + w) - φ y₀) * a y₀)) := by
      field_simp
      ring
    rw [hkey, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr ha0')]
    calc (a y₀)⁻¹ * |0 - 0 - (fderiv ℝ G (P y₀) (point w 0) + (φ (y₀ + w) - φ y₀) * a y₀)|
        ≤ (c / 2)⁻¹ * (ε' * ((1 + K) * ‖w‖)) := by
          gcongr
          exact hw.trans (mul_le_mul_of_nonneg_left hnormP hε'0.le)
      _ = ε * ‖w‖ := by
          rw [hε']
          field_simp
  have hDcont : ContinuousOn D (ball 0 ρ) := by
    have h1 : ContinuousOn (fun y ↦ fderiv ℝ G (P y)) (ball 0 ρ) :=
      hDGc.comp hPcont (fun y hy ↦ hPball y hy)
    have h2 : ContinuousOn a (ball 0 ρ) := h1.clm_apply continuousOn_const
    have h3 : ContinuousOn (fun y ↦ (a y)⁻¹) (ball 0 ρ) :=
      h2.inv₀ (fun y hy ↦ by linarith [ha y hy])
    have h4 : ContinuousOn (fun y ↦ (fderiv ℝ G (P y)).comp (horizontalEmbedding m))
        (ball 0 ρ) := h1.clm_comp continuousOn_const
    exact h3.neg.smul h4
  have hC1 : ContDiffOn ℝ 1 φ (ball 0 ρ) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    refine ⟨fun y hy ↦ (hderiv y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hDcont.congr (fun y hy ↦ (hderiv y hy).fderiv)
  refine ⟨φ, ρ, h, hρ, hh, ?_, hC1, hφ00, ?_, fun y hy ↦ abs_lt.mpr ⟨(hφI y hy).1, (hφI y hy).2⟩,
    ?_⟩
  · intro z hz
    apply hsr
    rw [mem_closedBall, dist_zero_right]
    have := norm_le_norm_horizontal_add_abs_last z
    have h1 : ‖horizontal z‖ < ρ := mem_ball_zero_iff.mp hz.1
    have h2 : |z (Fin.last m)| < h := abs_lt.mpr ⟨hz.2.1, hz.2.2⟩
    linarith
  · rw [(hderiv 0 (mem_ball_self hρ)).fderiv]
    ext v
    rw [hDapp]
    have hP0 : P 0 = 0 := by simp only [hP_def, hφ00, hpt00]
    rw [hP0, hGh v, mul_zero]
    rfl
  · intro z hz
    have hz' := hsign (horizontal z) hz.1 (z (Fin.last m)) ⟨hz.2.1.le, hz.2.2.le⟩
    rwa [point_horizontal_last] at hz'

/-- The Householder frame sending `e_n` to the unit vector `n`. -/
def householderFrame {m : ℕ} (n : Space (m + 1)) : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1) :=
  Submodule.reflection (ℝ ∙ (verticalDirection m - n))ᗮ

theorem householderFrame_verticalDirection {m : ℕ} {n : Space (m + 1)} (hn : ‖n‖ = 1) :
    householderFrame n (verticalDirection m) = n :=
  Submodule.reflection_sub (by rw [norm_verticalDirection, hn])

/-- **The graph chart of a `C¹` boundary point.** In the frame `z ↦ Q z + x`, where `Q e_n` is
the inner unit normal, `E` is a.e. the supergraph of a `C¹` function `φ` with `φ 0 = 0` and
`Dφ(0) = 0` on a cylinder. -/
theorem IsC1BoundaryPoint.exists_graphChart {m : ℕ} {E : Set (Space (m + 1))}
    {x : Space (m + 1)} (hx : IsC1BoundaryPoint E x) :
    ∃ (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (φ : Space m → ℝ) (ρ h : ℝ), 0 < ρ ∧ 0 < h ∧
      ContDiffOn ℝ 1 φ (ball 0 ρ) ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      (∀ y ∈ ball (0 : Space m) ρ, |φ y| < h) ∧
      ∀ᵐ z ∂volume, z ∈ cylinderSet (ball (0 : Space m) ρ) h →
        (Q z + x ∈ E ↔ φ (horizontal z) < z (Fin.last m)) := by
  obtain ⟨F, r, hr, hF, hFx, hDF, hae⟩ := hx
  set g := (toDual ℝ (Space (m + 1))).symm (fderiv ℝ F x) with hg_def
  have hgF : ∀ v, fderiv ℝ F x v = inner ℝ g v := fun v ↦ toDual_symm_apply.symm
  have hg0 : g ≠ 0 := by
    intro h0
    apply hDF
    ext v
    rw [hgF, h0, inner_zero_left]
    rfl
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg0
  set n := ‖g‖⁻¹ • g with hn_def
  have hn : ‖n‖ = 1 := by
    rw [hn_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hgn.ne']
  set Q := householderFrame n with hQ_def
  have hQe : Q (verticalDirection m) = n := householderFrame_verticalDirection hn
  set G : Space (m + 1) → ℝ := fun z ↦ F (Q z + x) with hG_def
  have hmaps : MapsTo (fun z ↦ Q z + x) (ball (0 : Space (m + 1)) r) (ball x r) := by
    intro z hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right, LinearIsometryEquiv.norm_map]
    exact mem_ball_zero_iff.mp hz
  have hA : ContDiff ℝ 1 (fun z : Space (m + 1) ↦ Q z + x) :=
    Q.toContinuousLinearEquiv.contDiff.add contDiff_const
  have hG : ContDiffOn ℝ 1 G (ball 0 r) := hF.comp hA.contDiffOn hmaps
  have hG0 : G 0 = 0 := by simp [hG_def, hFx]
  have hFd : HasFDerivAt F (fderiv ℝ F x) x :=
    ((hF.differentiableOn one_ne_zero) x (mem_ball_self hr)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hr)) |>.hasFDerivAt
  have hAd : HasFDerivAt (fun z : Space (m + 1) ↦ Q z + x)
      (Q.toContinuousLinearEquiv : Space (m + 1) →L[ℝ] Space (m + 1)) 0 :=
    (Q.toContinuousLinearEquiv : Space (m + 1) →L[ℝ] Space (m + 1)).hasFDerivAt.add_const x
  have hGd : fderiv ℝ G 0 = (fderiv ℝ F x).comp
      (Q.toContinuousLinearEquiv : Space (m + 1) →L[ℝ] Space (m + 1)) := by
    have h1 : HasFDerivAt F (fderiv ℝ F x) (Q 0 + x) := by simpa using hFd
    exact (h1.comp 0 hAd).fderiv
  have hGn : 0 < fderiv ℝ G 0 (verticalDirection m) := by
    rw [hGd, ContinuousLinearMap.comp_apply]
    change 0 < fderiv ℝ F x (Q (verticalDirection m))
    rw [hQe, hgF, hn_def, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have : ‖g‖⁻¹ * ‖g‖ ^ 2 = ‖g‖ := by field_simp
    rw [this]
    exact hgn
  have hGh : ∀ v : Space m, fderiv ℝ G 0 (point v 0) = 0 := by
    intro v
    rw [hGd, ContinuousLinearMap.comp_apply]
    change fderiv ℝ F x (Q (point v 0)) = 0
    have hgn' : g = ‖g‖ • n := by
      rw [hn_def, smul_smul, mul_inv_cancel₀ hgn.ne', one_smul]
    rw [hgF, hgn', real_inner_smul_left, ← hQe, LinearIsometryEquiv.inner_map_map,
      real_inner_comm, inner_verticalDirection_right, last_point, mul_zero]
  obtain ⟨φ, ρ, h, hρ, hh, hcyl, hφ, hφ0, hDφ0, hφh, hsign⟩ :=
    exists_C1_graph_of_fderiv_last_pos hr hG hG0 hGn hGh
  refine ⟨Q, φ, ρ, h, hρ, hh, hφ, hφ0, hDφ0, hφh, ?_⟩
  have hmp := measurePreserving_affineIsometryHomeomorph Q x
  have hae' := hmp.quasiMeasurePreserving.ae hae
  filter_upwards [hae'] with z hz hzc
  have hzr : z ∈ ball (0 : Space (m + 1)) r := hcyl hzc
  rw [affineIsometryHomeomorph_apply] at hz
  rw [hz (hmaps hzr)]
  exact hsign z hzc

/-! ### The weak minimal surface equation -/

/-- The tangent-line bound for the area integrand. -/
theorem sqrt_one_add_norm_add_smul_sq_le {d : ℕ} (v w : Space d) (t : ℝ) :
    Real.sqrt (1 + ‖v + t • w‖ ^ 2) ≤ Real.sqrt (1 + ‖v‖ ^ 2) +
      t * (inner ℝ v w / Real.sqrt (1 + ‖v‖ ^ 2)) + t ^ 2 * (‖w‖ ^ 2 / 2) := by
  set X₀ := 1 + ‖v‖ ^ 2 with hX₀
  set X := 1 + ‖v + t • w‖ ^ 2 with hX_def
  set s₀ := Real.sqrt X₀ with hs₀_def
  have hX₀1 : 1 ≤ X₀ := by nlinarith [sq_nonneg ‖v‖]
  have hs₀ : 1 ≤ s₀ := Real.one_le_sqrt.mpr hX₀1
  have hs₀sq : s₀ ^ 2 = X₀ := Real.sq_sqrt (by linarith)
  have hX0 : 0 ≤ X := by positivity
  have hsX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0
  have hX : X = X₀ + 2 * t * inner ℝ v w + t ^ 2 * ‖w‖ ^ 2 := by
    rw [hX_def, hX₀, norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow,
      Real.norm_eq_abs, sq_abs]
    ring
  have hs₀p : 0 < s₀ := by linarith
  have hs₀ne : s₀ ≠ 0 := hs₀p.ne'
  have htan : Real.sqrt X ≤ s₀ + (X - X₀) / (2 * s₀) := by
    have hpos : 0 < 2 * s₀ := by linarith
    have hrw : s₀ + (X - X₀) / (2 * s₀) = (2 * s₀ * s₀ + (X - X₀)) / (2 * s₀) := by
      field_simp
    rw [hrw, le_div_iff₀ hpos]
    nlinarith [sq_nonneg (Real.sqrt X - s₀), Real.sqrt_nonneg X]
  calc Real.sqrt X ≤ s₀ + (X - X₀) / (2 * s₀) := htan
    _ = s₀ + t * (inner ℝ v w / s₀) + t ^ 2 * (‖w‖ ^ 2 / (2 * s₀)) := by
        rw [hX]
        field_simp
        ring
    _ ≤ s₀ + t * (inner ℝ v w / s₀) + t ^ 2 * (‖w‖ ^ 2 / 2) := by
        gcongr
        linarith

theorem gradient_add_const_mul {d : ℕ} {f g : Space d → ℝ} {y : Space d}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) (t : ℝ) :
    gradient (fun y ↦ f y + t * g y) y = gradient f y + t • gradient g y := by
  have hd : HasFDerivAt (fun y ↦ f y + t * g y) (fderiv ℝ f y + t • fderiv ℝ g y) y :=
    (hf.hasFDerivAt).add ((hg.hasFDerivAt).const_mul t)
  simp only [gradient]
  rw [hd.fderiv, map_add, map_smulₛₗ, conj_trivial]

/-- If `0 ≤ t I + t² C` for all small `|t|`, then `I = 0`. -/
theorem eq_zero_of_forall_small_quadratic {I C t₀ : ℝ} (ht₀ : 0 < t₀) (hC : 0 ≤ C)
    (h : ∀ t, |t| ≤ t₀ → 0 ≤ t * I + t ^ 2 * C) : I = 0 := by
  by_contra hI
  have hIa : 0 < |I| := abs_pos.mpr hI
  set s := min t₀ (|I| / (2 * (C + 1))) with hs_def
  have hs : 0 < s := lt_min ht₀ (by positivity)
  have hst : s ≤ t₀ := min_le_left _ _
  have hsI : s ≤ |I| / (2 * (C + 1)) := min_le_right _ _
  have hsC : s * C < |I| := by
    have h1 : s * C ≤ |I| / (2 * (C + 1)) * C := mul_le_mul_of_nonneg_right hsI hC
    have h2 : |I| / (2 * (C + 1)) * C < |I| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases lt_or_gt_of_ne hI with hneg | hpos
  · have := h s (by rw [abs_of_pos hs]; exact hst)
    rw [abs_of_neg hneg] at hsC
    nlinarith
  · have := h (-s) (by rw [abs_neg, abs_of_pos hs]; exact hst)
    rw [abs_of_pos hpos] at hsC
    nlinarith

/-- **The weak minimal surface equation.** If a local perimeter minimizer in the whole space is
a.e. the supergraph of a `C¹` function `φ` on the cylinder `B_ρ × (-h, h)`, with `|φ| < h`, then
`φ` is a weak solution of `div (∇φ / √(1 + |∇φ|²)) = 0` on `B_ρ`. -/
theorem IsLocalPerimeterMinimizer.isWeakSolution_minimalSurfaceFlux_of_graph {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) {φ : Space m → ℝ} {ρ h : ℝ} (hρ : 0 < ρ)
    (hφ : ContDiffOn ℝ 1 φ (ball 0 ρ)) (hφh : ∀ y ∈ ball (0 : Space m) ρ, |φ y| < h)
    (hchart : ∀ᵐ z ∂volume, z ∈ cylinderSet (ball (0 : Space m) ρ) h →
      (z ∈ E ↔ φ (horizontal z) < z (Fin.last m))) :
    IsWeakSolution minimalSurfaceFlux φ (ball 0 ρ) := by
  intro ψ hψ hψc hψs
  -- a smaller ball containing the support
  obtain ⟨ρ₀, hρ₀, hψρ₀⟩ := exists_lt_subset_ball (isClosed_tsupport ψ) hψs
  set ρ₁ := max ρ₀ (ρ / 2) with hρ₁_def
  have hρ₁ : ρ₁ < ρ := max_lt hρ₀ (by linarith)
  have hρ₁0 : 0 < ρ₁ := lt_max_of_lt_right (by linarith)
  have hψρ₁ : tsupport ψ ⊆ ball 0 ρ₁ := hψρ₀.trans (ball_subset_ball (le_max_left _ _))
  set ρ₂ := (ρ₁ + ρ) / 2 with hρ₂_def
  have hρ₁₂ : ρ₁ < ρ₂ := by linarith
  have hρ₂ : ρ₂ < ρ := by linarith
  -- a height margin
  obtain ⟨H₀, hH₀h, hH₀⟩ : ∃ H₀ < h, ∀ y ∈ closedBall (0 : Space m) ρ₂, |φ y| ≤ H₀ := by
    have hcomp : IsCompact (closedBall (0 : Space m) ρ₂) := isCompact_closedBall 0 ρ₂
    have hne : (closedBall (0 : Space m) ρ₂).Nonempty := ⟨0, mem_closedBall_self (by linarith)⟩
    have hcont : ContinuousOn (fun y ↦ |φ y|) (closedBall (0 : Space m) ρ₂) :=
      (hφ.continuousOn.mono (closedBall_subset_ball hρ₂)).abs
    obtain ⟨y₀, hy₀, hmax⟩ := hcomp.exists_isMaxOn hne hcont
    exact ⟨|φ y₀|, hφh y₀ (closedBall_subset_ball hρ₂ hy₀), fun y hy ↦ hmax hy⟩
  -- a global `C¹` extension
  let χ : ContDiffBump (0 : Space m) := ⟨ρ₁, ρ₂, hρ₁0, hρ₁₂⟩
  have hχs : tsupport (χ : Space m → ℝ) ⊆ ball 0 ρ := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball hρ₂
  set φt : Space m → ℝ := fun y ↦ φ y * χ y with hφt_def
  have hφt : ContDiff ℝ 1 φt := contDiff_mul_of_tsupport_subset isOpen_ball hφ χ.contDiff hχs
  have hφteq : ∀ y ∈ ball (0 : Space m) ρ₁, φt y = φ y := by
    intro y hy
    simp only [hφt_def, χ.one_of_mem_closedBall (ball_subset_closedBall hy), mul_one]
  have hφtH : ∀ y ∈ ball (0 : Space m) ρ₁, |φt y| ≤ H₀ := fun y hy ↦ by
    rw [hφteq y hy]
    exact hH₀ y (ball_subset_closedBall.trans (closedBall_subset_closedBall hρ₁₂.le) hy)
  have hgradeq : ∀ y ∈ ball (0 : Space m) ρ₁, gradient φ y = gradient φt y := by
    intro y hy
    have hev : φt =ᶠ[𝓝 y] φ := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact hφteq z hz
    simp only [gradient, hev.fderiv_eq]
  -- the size of `ψ` and the admissible range of `t`
  obtain ⟨S, hS⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  set t₀ := (h - H₀) / (2 * (S + 1)) with ht₀_def
  have ht₀ : 0 < t₀ := by
    have : 0 < h - H₀ := by linarith
    positivity
  set h₁ := (H₀ + h) / 2 with hh₁_def
  have hH₀0 : 0 ≤ H₀ := (abs_nonneg _).trans (hH₀ 0 (mem_closedBall_self (by linarith)))
  have hh₁ : h₁ < h := by linarith
  have hbt_small : ∀ t, |t| ≤ t₀ → ∀ y ∈ ball (0 : Space m) ρ₁, |φt y + t * ψ y| < h₁ := by
    intro t ht y hy
    have h1 := hφtH y hy
    have h2 : |t * ψ y| ≤ t₀ * S := by
      rw [abs_mul]
      exact mul_le_mul ht ((Real.norm_eq_abs _).symm ▸ hS y) (abs_nonneg _) ht₀.le
    have h3 : t₀ * S < (h - H₀) / 2 := by
      rw [ht₀_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    calc |φt y + t * ψ y| ≤ |φt y| + |t * ψ y| := abs_add_le _ _
      _ < h₁ := by rw [hh₁_def]; linarith
  -- the domain and the compact perturbation set
  set V := cylinderSet (ball (0 : Space m) ρ₁) h with hV_def
  have hVo : IsOpen V := isOpen_cylinderSet isOpen_ball h
  set K := (fun p : Space m × ℝ ↦ point p.1 p.2) '' (tsupport ψ ×ˢ Icc (-h₁) h₁) with hK_def
  have hK : IsCompact K := (hψc.prod isCompact_Icc).image pointContinuousLinearMap.continuous
  have hKV : K ⊆ V := by
    rintro _ ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
    exact point_mem_cylinderSet.mpr ⟨hψρ₁ hy, by linarith [ht.1], by linarith [ht.2]⟩
  have hgraph : ∀ c : Space m → ℝ, (∀ y ∈ ball (0 : Space m) ρ₁, |c y| < h) →
      {y | point y (c y) ∈ V} = ball 0 ρ₁ := by
    intro c hc
    ext y
    simp only [Set.mem_ofPred_eq, hV_def, point_mem_cylinderSet]
    constructor
    · exact fun h' ↦ h'.1
    · intro hy
      exact ⟨hy, (abs_lt.mp (hc y hy)).1, (abs_lt.mp (hc y hy)).2⟩
  -- the area functional
  set A : ℝ → ℝ := fun t ↦ ∫ y in ball (0 : Space m) ρ₁,
    graphAreaDensity (fun y ↦ φt y + t * ψ y) y with hA_def
  have hbt : ∀ t : ℝ, ContDiff ℝ 1 (fun y ↦ φt y + t * ψ y) := fun t ↦
    hφt.add (contDiff_const.mul hψ)
  have hAint : ∀ t : ℝ, IntegrableOn (graphAreaDensity (fun y ↦ φt y + t * ψ y))
      (ball (0 : Space m) ρ₁) := fun t ↦
    ((continuous_graphAreaDensity (hbt t)).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ρ₁)).mono_set ball_subset_closedBall
  have hcomp : ∀ t, |t| ≤ t₀ → A 0 ≤ A t := by
    intro t ht
    set bt : Space m → ℝ := fun y ↦ φt y + t * ψ y with hbt_def
    set D := (E \ V) ∪ (epigraph bt ∩ V) with hD_def
    have hD : MeasurableSet D :=
      (hmin.measurableSet.diff hVo.measurableSet).union
        ((isOpen_epigraph (hbt t).continuous).measurableSet.inter hVo.measurableSet)
    have hED : ∀ᵐ z ∂volume, z ∉ K → (z ∈ E ↔ z ∈ D) := by
      filter_upwards [hchart] with z hz hzK
      by_cases hzV : z ∈ V
      · have hzc : z ∈ cylinderSet (ball (0 : Space m) ρ) h :=
          ⟨ball_subset_ball hρ₁.le hzV.1, hzV.2⟩
        have hπ : horizontal z ∈ ball (0 : Space m) ρ₁ := hzV.1
        rw [hz hzc, ← hφteq _ hπ]
        have hDz : z ∈ D ↔ bt (horizontal z) < z (Fin.last m) := by
          simp only [hD_def, mem_union, Set.mem_sdiff, mem_inter_iff, hzV, not_true_eq_false,
            and_false, and_true, false_or, epigraph, Set.mem_ofPred_eq]
        rw [hDz]
        by_cases hψz : ψ (horizontal z) = 0
        · simp only [hbt_def, hψz, mul_zero, add_zero]
        · have hzs : horizontal z ∈ tsupport ψ := subset_tsupport ψ hψz
          have hzn : z (Fin.last m) ∉ Icc (-h₁) h₁ := by
            intro hmem
            exact hzK ⟨(horizontal z, z (Fin.last m)), ⟨hzs, hmem⟩, point_horizontal_last z⟩
          have h1 := abs_lt.mp (hbt_small t ht _ hπ)
          have h2 : |φt (horizontal z)| < h₁ := by
            have := hφtH _ hπ
            linarith
          have h2' := abs_lt.mp h2
          simp only [mem_Icc, not_and_or, not_le] at hzn
          simp only [hbt_def]
          rcases hzn with hlt | hgt
          · constructor <;> intro _ <;> linarith
          · constructor <;> intro _ <;> linarith
      · simp only [hD_def, mem_union, Set.mem_sdiff, mem_inter_iff, hzV, not_false_eq_true,
          and_true, and_false, or_false]
    have hP := hmin.minimizes V D K hVo (subset_univ _) hD hK hKV hED
    have h1 : variationalPerimeter b E V = variationalPerimeter b (epigraph φt) V := by
      apply variationalPerimeter_congr_ae_on
      filter_upwards [hchart] with z hz hzV
      have hzc : z ∈ cylinderSet (ball (0 : Space m) ρ) h :=
        ⟨ball_subset_ball hρ₁.le hzV.1, hzV.2⟩
      rw [hz hzc, ← hφteq _ hzV.1]
      rfl
    have h2 : variationalPerimeter b D V = variationalPerimeter b (epigraph bt) V := by
      apply variationalPerimeter_congr_ae_on
      filter_upwards with z hzV
      simp only [hD_def, mem_union, Set.mem_sdiff, mem_inter_iff, hzV, not_true_eq_false,
        and_false, and_true, false_or]
    have hφt_small : ∀ y ∈ ball (0 : Space m) ρ₁, |φt y| < h := fun y hy ↦
      (hφtH y hy).trans_lt hH₀h
    have hbt_small' : ∀ y ∈ ball (0 : Space m) ρ₁, |bt y| < h := fun y hy ↦
      (hbt_small t ht y hy).trans hh₁
    rw [h1, h2, graph_perimeter_eq_area b hφt hVo, graph_perimeter_eq_area b (hbt t) hVo,
      hgraph φt hφt_small, hgraph bt hbt_small'] at hP
    have hA0 : A 0 = ∫ y in ball (0 : Space m) ρ₁, graphAreaDensity φt y := by
      simp only [hA_def, zero_mul, add_zero]
    rw [hA0]
    have hint0 : IntegrableOn (graphAreaDensity φt) (ball (0 : Space m) ρ₁) :=
      ((continuous_graphAreaDensity hφt).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 ρ₁)).mono_set ball_subset_closedBall
    rw [← ofReal_integral_eq_lintegral_ofReal hint0
        (Eventually.of_forall fun y ↦ (graphAreaDensity_pos _ y).le),
      ← ofReal_integral_eq_lintegral_ofReal (hAint t)
        (Eventually.of_forall fun y ↦ (graphAreaDensity_pos _ y).le)] at hP
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun y ↦
      (graphAreaDensity_pos _ y).le)).mp hP
  -- the quadratic upper bound
  set v : Space m → Space m := gradient φt with hv_def
  set w : Space m → Space m := gradient ψ with hw_def
  have hvc : Continuous v := by
    have := (hφt.continuous_fderiv one_ne_zero)
    exact (toDual ℝ (Space m)).symm.continuous.comp this
  have hwc : Continuous w := by
    have := (hψ.continuous_fderiv one_ne_zero)
    exact (toDual ℝ (Space m)).symm.continuous.comp this
  have hgad : ∀ t y, graphAreaDensity (fun y ↦ φt y + t * ψ y) y =
      Real.sqrt (1 + ‖v y + t • w y‖ ^ 2) := by
    intro t y
    rw [graphAreaDensity, gradient_add_const_mul (hφt.differentiable one_ne_zero y)
      (hψ.differentiable one_ne_zero y)]
  have hgadf : ∀ t, graphAreaDensity (fun y ↦ φt y + t * ψ y) =
      fun y ↦ Real.sqrt (1 + ‖v y + t • w y‖ ^ 2) := fun t ↦ funext (hgad t)
  set I := ∫ y in ball (0 : Space m) ρ₁, inner ℝ (v y) (w y) / Real.sqrt (1 + ‖v y‖ ^ 2)
    with hI_def
  set C := ∫ y in ball (0 : Space m) ρ₁, ‖w y‖ ^ 2 / 2 with hC_def
  have hC0 : 0 ≤ C := integral_nonneg fun y ↦ by positivity
  have hintI : IntegrableOn (fun y ↦ inner ℝ (v y) (w y) / Real.sqrt (1 + ‖v y‖ ^ 2))
      (ball (0 : Space m) ρ₁) := by
    have hc : Continuous (fun y ↦ inner ℝ (v y) (w y) / Real.sqrt (1 + ‖v y‖ ^ 2)) := by
      refine (hvc.inner hwc).div (Real.continuous_sqrt.comp (continuous_const.add
        (hvc.norm.pow 2))) fun y ↦ ?_
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 ρ₁)).mono_set
      ball_subset_closedBall
  have hintC : IntegrableOn (fun y ↦ ‖w y‖ ^ 2 / 2) (ball (0 : Space m) ρ₁) :=
    (((hwc.norm.pow 2).div_const 2).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ρ₁)).mono_set ball_subset_closedBall
  have hquad : ∀ t, |t| ≤ t₀ → 0 ≤ t * I + t ^ 2 * C := by
    intro t ht
    have hle := hcomp t ht
    have hA0' : A 0 = ∫ y in ball (0 : Space m) ρ₁, Real.sqrt (1 + ‖v y‖ ^ 2) := by
      show (∫ y in ball (0 : Space m) ρ₁, graphAreaDensity (fun y ↦ φt y + 0 * ψ y) y) = _
      simp only [hgad, zero_smul, add_zero]
    have hAt : A t = ∫ y in ball (0 : Space m) ρ₁, Real.sqrt (1 + ‖v y + t • w y‖ ^ 2) := by
      show (∫ y in ball (0 : Space m) ρ₁, graphAreaDensity (fun y ↦ φt y + t * ψ y) y) = _
      simp only [hgad]
    have hint0 : IntegrableOn (fun y ↦ Real.sqrt (1 + ‖v y‖ ^ 2)) (ball (0 : Space m) ρ₁) := by
      have := hAint 0
      rw [hgadf] at this
      simpa only [zero_smul, add_zero] using this
    have hi1 : IntegrableOn (fun y ↦ Real.sqrt (1 + ‖v y‖ ^ 2) +
        t * (inner ℝ (v y) (w y) / Real.sqrt (1 + ‖v y‖ ^ 2))) (ball (0 : Space m) ρ₁) :=
      hint0.add (hintI.const_mul t)
    have hi2 : IntegrableOn (fun y ↦ Real.sqrt (1 + ‖v y‖ ^ 2) +
        t * (inner ℝ (v y) (w y) / Real.sqrt (1 + ‖v y‖ ^ 2)) + t ^ 2 * (‖w y‖ ^ 2 / 2))
        (ball (0 : Space m) ρ₁) := hi1.add (hintC.const_mul _)
    have hiAt : IntegrableOn (fun y ↦ Real.sqrt (1 + ‖v y + t • w y‖ ^ 2))
        (ball (0 : Space m) ρ₁) := by
      have := hAint t
      rwa [hgadf] at this
    have hsum : ∫ y in ball (0 : Space m) ρ₁, (Real.sqrt (1 + ‖v y‖ ^ 2) +
        t * (inner ℝ (v y) (w y) / Real.sqrt (1 + ‖v y‖ ^ 2)) + t ^ 2 * (‖w y‖ ^ 2 / 2)) =
        A 0 + t * I + t ^ 2 * C := by
      rw [integral_add hi1 (hintC.const_mul _), integral_add hint0 (hintI.const_mul t),
        integral_const_mul, integral_const_mul, hA0']
    have hupper : A t ≤ A 0 + t * I + t ^ 2 * C := by
      rw [hAt, ← hsum]
      exact setIntegral_mono_on hiAt hi2 measurableSet_ball
        fun y _ ↦ sqrt_one_add_norm_add_smul_sq_le (v y) (w y) t
    linarith
  have hI0 : I = 0 := eq_zero_of_forall_small_quadratic ht₀ hC0 hquad
  -- the weak form
  have hflux : ∀ y, inner ℝ (minimalSurfaceFlux (gradient φ y)) (w y) =
      (ball (0 : Space m) ρ₁).indicator
        (fun y ↦ inner ℝ (v y) (w y) / Real.sqrt (1 + ‖v y‖ ^ 2)) y := by
    intro y
    by_cases hy : y ∈ ball (0 : Space m) ρ₁
    · rw [indicator_of_mem hy, hgradeq y hy, minimalSurfaceFlux, real_inner_smul_left]
      ring
    · rw [indicator_of_notMem hy]
      have hψy : y ∉ tsupport ψ := fun h' ↦ hy (hψρ₁ h')
      have hgψ : w y = 0 := by
        show gradient ψ y = 0
        simp only [gradient, fderiv_of_notMem_tsupport ℝ hψy, map_zero]
      rw [hgψ, inner_zero_right]
  have hfun : (fun y ↦ inner ℝ (minimalSurfaceFlux (gradient φ y)) (w y)) =
      (ball (0 : Space m) ρ₁).indicator
        (fun y ↦ inner ℝ (v y) (w y) / Real.sqrt (1 + ‖v y‖ ^ 2)) := funext hflux
  show ∫ y, inner ℝ (minimalSurfaceFlux (gradient φ y)) (w y) = 0
  rw [hfun, integral_indicator measurableSet_ball]
  exact hI0

/-! ### Smooth graph charts -/

theorem horizontal_add_smul_verticalDirection_eq {m : ℕ} (z : Space (m + 1)) (s : ℝ) :
    horizontal (z + s • verticalDirection m) = horizontal z := by
  have h := horizontal_sub_smul_verticalDirection z (-s)
  rwa [neg_smul, sub_neg_eq_add] at h

theorem last_add_smul_verticalDirection_eq {m : ℕ} (z : Space (m + 1)) (s : ℝ) :
    (z + s • verticalDirection m) (Fin.last m) = z (Fin.last m) + s := by
  have h := last_sub_smul_verticalDirection z (-s)
  rwa [neg_smul, sub_neg_eq_add, sub_neg_eq_add] at h

/-- The base point lies in the domain of its graph chart. -/
theorem mem_graphChartDomain_self {m : ℕ} (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (x : Space (m + 1)) {ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 < h) :
    x ∈ (fun y ↦ Q.symm (y - x)) ⁻¹' cylinderSet (ball (0 : Space m) ρ) h := by
  have h0 : horizontal (0 : Space (m + 1)) = 0 := by
    rw [← horizontalContinuousLinearMap_apply', map_zero]
  simp only [mem_preimage, sub_self, map_zero, mem_cylinderSet, h0, mem_ball_self hρ, true_and]
  simp [hh]

/-- **A smooth graph chart is a smooth boundary chart.** If, in the frame `z ↦ Q z + x`, the set
`E` is a.e. the supergraph of a `C^∞` function `φ` over the cylinder `B_ρ × (-h, h)`, then
`F(y) = t - φ(y')`, where `(y', t) = Q⁻¹ (y - x)`, is a smooth boundary chart of `E` on the
image `{y | Q⁻¹ (y - x) ∈ B_ρ × (-h, h)}` of the cylinder. -/
theorem isSmoothBoundaryChart_of_graphChart {m : ℕ} {E : Set (Space (m + 1))}
    {x : Space (m + 1)} (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {φ : Space m → ℝ} {ρ h : ℝ}
    (hφ : ContDiffOn ℝ ∞ φ (ball 0 ρ))
    (hchart : ∀ᵐ z ∂volume, z ∈ cylinderSet (ball (0 : Space m) ρ) h →
      (Q z + x ∈ E ↔ φ (horizontal z) < z (Fin.last m))) :
    IsSmoothBoundaryChart E ((fun y ↦ Q.symm (y - x)) ⁻¹' cylinderSet (ball (0 : Space m) ρ) h)
      (fun y ↦ Q.symm (y - x) (Fin.last m) - φ (horizontal (Q.symm (y - x)))) := by
  set T : Space (m + 1) → Space (m + 1) := fun y ↦ Q.symm (y - x) with hT_def
  set C := cylinderSet (ball (0 : Space m) ρ) h with hC_def
  set F : Space (m + 1) → ℝ := fun y ↦ T y (Fin.last m) - φ (horizontal (T y)) with hF_def
  show IsSmoothBoundaryChart E (T ⁻¹' C) F
  have hFT : ∀ y, F y = T y (Fin.last m) - φ (horizontal (T y)) := fun y ↦ rfl
  have hTc : ContDiff ℝ ∞ T := Q.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hUo : IsOpen (T ⁻¹' C) := (isOpen_cylinderSet isOpen_ball h).preimage hTc.continuous
  have hFc : ContDiffOn ℝ ∞ F (T ⁻¹' C) := by
    have h1 : ContDiff ℝ ∞ (fun y ↦ T y (Fin.last m)) :=
      (contDiff_piLp_apply (p := 2) (i := Fin.last m)).comp hTc
    have h2 : ContDiffOn ℝ ∞ (φ ∘ (horizontalContinuousLinearMap ∘ T)) (T ⁻¹' C) :=
      hφ.comp (horizontalContinuousLinearMap.contDiff.comp hTc).contDiffOn fun y hy ↦ hy.1
    exact h1.contDiffOn.sub h2
  have hu : ∀ y (s : ℝ), F (y + s • Q (verticalDirection m)) = F y + s := by
    intro y s
    have hTy : T (y + s • Q (verticalDirection m)) = T y + s • verticalDirection m := by
      show Q.symm (y + s • Q (verticalDirection m) - x) = Q.symm (y - x) + s • verticalDirection m
      rw [show y + s • Q (verticalDirection m) - x = (y - x) + s • Q (verticalDirection m) by abel,
        map_add, map_smul, LinearIsometryEquiv.symm_apply_apply]
    rw [hFT, hFT, hTy, horizontal_add_smul_verticalDirection_eq,
      last_add_smul_verticalDirection_eq]
    ring
  refine ⟨hUo, hFc, fun y hy ↦ ?_, ?_⟩
  · have hFd : DifferentiableAt ℝ F y :=
      (hFc.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds hy)
    have h1 : fderiv ℝ F y (Q (verticalDirection m)) = 1 := by
      rw [← hFd.lineDeriv_eq_fderiv, lineDeriv]
      have hfun : (fun t : ℝ ↦ F (y + t • Q (verticalDirection m))) = fun t ↦ F y + t :=
        funext (hu y)
      rw [hfun]
      simp
    intro hg
    have h0 : fderiv ℝ F y = 0 := by
      have := congrArg (toDual ℝ (Space (m + 1))) hg
      rwa [gradient, LinearIsometryEquiv.apply_symm_apply, map_zero] at this
    rw [h0] at h1
    simp at h1
  · rw [ae_restrict_iff' hUo.measurableSet]
    have hmpT : MeasurePreserving T volume volume :=
      Q.symm.measurePreserving.comp (measurePreserving_sub_right volume x)
    filter_upwards [hmpT.quasiMeasurePreserving.ae hchart] with y hy hyU
    have hQT : Q (T y) + x = y := by
      show Q (Q.symm (y - x)) + x = y
      rw [LinearIsometryEquiv.apply_symm_apply, sub_add_cancel]
    have hy' := hy hyU
    rw [hQT] at hy'
    rw [hy', hFT, sub_pos]

/-! ### Minimal graph charts of local minimizers -/

/-- **The minimal graph chart of a `C¹` boundary point.** At a `C¹` boundary point `x` of a local
perimeter minimizer in the whole space, in the frame `z ↦ Q z + x`, the minimizer is a.e. the
supergraph of a `C¹` function `φ` with `φ 0 = 0`, `Dφ(0) = 0` on a cylinder `B_ρ × (-h, h)`,
and `φ` is a weak solution of the minimal surface equation on `B_ρ`. -/
theorem IsLocalPerimeterMinimizer.exists_minimalGraphChart {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    {x : Space (m + 1)} (hmin : IsLocalPerimeterMinimizer b E univ)
    (hx : IsC1BoundaryPoint E x) :
    ∃ (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (φ : Space m → ℝ) (ρ h : ℝ), 0 < ρ ∧ 0 < h ∧
      ContDiffOn ℝ 1 φ (ball 0 ρ) ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      (∀ y ∈ ball (0 : Space m) ρ, |φ y| < h) ∧
      (∀ᵐ z ∂volume, z ∈ cylinderSet (ball (0 : Space m) ρ) h →
        (Q z + x ∈ E ↔ φ (horizontal z) < z (Fin.last m))) ∧
      IsWeakSolution minimalSurfaceFlux φ (ball 0 ρ) := by
  obtain ⟨Q, φ, ρ, h, hρ, hh, hφ, hφ0, hDφ0, hφh, hchart⟩ := hx.exists_graphChart
  refine ⟨Q, φ, ρ, h, hρ, hh, hφ, hφ0, hDφ0, hφh, hchart, ?_⟩
  have hmin' := hmin.preimage_affineIsometry (by omega) Q x
  rw [preimage_univ] at hmin'
  refine hmin'.isWeakSolution_minimalSurfaceFlux_of_graph hρ hφ hφh ?_
  filter_upwards [hchart] with z hz hzc
  rw [mem_preimage, affineIsometryHomeomorph_apply]
  exact hz hzc

theorem eq_of_space_zero (a b : Space 0) : a = b := by
  ext i
  exact i.elim0

/-- Every function on the zero-dimensional space is smooth. -/
theorem contDiffOn_of_space_zero (φ : Space 0 → ℝ) (s : Set (Space 0)) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n φ s := by
  have hφ : φ = fun _ ↦ φ 0 := funext fun y ↦ congrArg φ (eq_of_space_zero y 0)
  rw [hφ]
  exact contDiffOn_const

/-- **Smooth charts at `C¹` boundary points of local minimizers.** If `C¹` weak solutions of the
minimal surface equation on balls are smooth, then every `C¹` boundary point of a local perimeter
minimizer in the whole space lies in a smooth boundary chart. -/
theorem IsLocalPerimeterMinimizer.exists_isSmoothBoundaryChart_of_minimalSurface {m : ℕ}
    (hreg : ∀ (ρ : ℝ) (φ : Space m → ℝ), 0 < m → 0 < ρ → ContDiffOn ℝ 1 φ (ball 0 ρ) →
      IsWeakSolution minimalSurfaceFlux φ (ball 0 ρ) → ContDiffOn ℝ ∞ φ (ball 0 ρ))
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    {x : Space (m + 1)} (hmin : IsLocalPerimeterMinimizer b E univ)
    (hx : IsC1BoundaryPoint E x) :
    ∃ U F, x ∈ U ∧ IsSmoothBoundaryChart E U F := by
  obtain ⟨Q, φ, ρ, h, hρ, hh, hφ, -, -, -, hchart, hweak⟩ := hmin.exists_minimalGraphChart hx
  have hφ' : ContDiffOn ℝ ∞ φ (ball 0 ρ) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact contDiffOn_of_space_zero φ _ _
    · exact hreg ρ φ hm hρ hφ hweak
  exact ⟨_, _, mem_graphChartDomain_self Q x hρ hh,
    isSmoothBoundaryChart_of_graphChart Q hφ' hchart⟩

/-- **`C1RegularSmoothHyp` from the regularity of minimal graphs.** It suffices that `C¹` weak
solutions of the minimal surface equation on balls of `ℝ^m`, `m ≥ 1`, are `C^∞` there. -/
theorem c1RegularSmoothHyp_of_minimalSurface
    (hreg : ∀ (m : ℕ) (ρ : ℝ) (φ : Space m → ℝ), 0 < m → 0 < ρ →
      ContDiffOn ℝ 1 φ (ball 0 ρ) → IsWeakSolution minimalSurfaceFlux φ (ball 0 ρ) →
      ContDiffOn ℝ ∞ φ (ball 0 ρ)) :
    C1RegularSmoothHyp := by
  intro d E x hmin hx
  rcases d with _ | m
  · exfalso
    obtain ⟨F, r, -, -, -, hF, -⟩ := hx
    apply hF
    ext v
    rw [eq_of_space_zero v 0]
    simp
  · exact hmin.exists_isSmoothBoundaryChart_of_minimalSurface (hreg m) hx

end SerrinEpigraph
