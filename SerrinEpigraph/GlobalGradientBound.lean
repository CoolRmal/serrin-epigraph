module

public import SerrinEpigraph.BernsteinEstimate
public import SerrinEpigraph.StressStationarity
public import SerrinEpigraph.RadialEndpoint

/-!
# A global gradient bound from bounded solution values and constant Neumann data

Compact optimization is performed on the intersection of a unit ball with the closed
epigraph. The Bernstein estimate handles an interior maximum; the prescribed gradient
and the vanishing polynomial cutoff handle the two boundary pieces.
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter Metric
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The one-sided C1 hypothesis controls the ordinary reaction derivative at positive states. -/
theorem Hypotheses.reaction_deriv_bound_on_unit_interval (h : Hypotheses g u f κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Ioc (0 : ℝ) 1, deriv f s ≤ B := by
  have hd := h.reaction_contDiffOn.continuousOn_derivWithin (uniqueDiffOn_Ici (0 : ℝ)) le_rfl
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hd.mono (show Icc (0 : ℝ) 1 ⊆ Ici 0 from fun _ hs ↦ hs.1))
  refine ⟨max B 0, le_max_right _ _, fun s hs ↦ ?_⟩
  have hb := hB s ⟨hs.1.le, hs.2⟩
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hs.1)] at hb
  have hb' : |deriv f s| ≤ B := by simpa only [Real.norm_eq_abs] using hb
  exact (le_abs_self _).trans (hb'.trans (le_max_left _ _))

/-- Explicit gradient control from uniform bounds on the reaction and its derivative. -/
theorem RigidityHypotheses.gradient_sq_le_of_reaction_bounds
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hderiv : ∀ s ∈ Ioc (0 : ℝ) 1, deriv f s ≤ B)
    (hreact : ∀ s ∈ Icc (0 : ℝ) 1, ‖f s‖ ≤ M)
    {c : Space (m + 1)} (hc : c ∈ epigraph g) :
    ‖gradient u c‖ ^ 2 ≤ κ ^ 2 + (B + 2 * (m + 1 : ℝ) + 13) * (M + 1) := by
  let A := B + 2 * (m + 1 : ℝ) + 13
  let η := polynomialBallBarrier c 1
  let Q := fun x ↦ η x * (‖gradientWithin u (closure (epigraph g)) x‖ ^ 2 / 2) +
    A * (u x ^ 2 / 2)
  let K := closure (epigraph g) ∩ closedBall c 1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hη : ContDiff ℝ 2 η := contDiff_polynomialBallBarrier c 1
  have hQc : ContinuousOn Q (closure (epigraph g)) :=
    ((hη.continuous.continuousOn.mul ((h.closed_gradient_continuousOn.norm.pow 2).div_const 2)).add
      (continuousOn_const.mul ((h.solution_contDiffOn_closure.continuousOn.pow 2).div_const 2)))
  have hK : IsCompact K := (isCompact_closedBall c 1).inter_left isClosed_closure
  have hcK : c ∈ K := ⟨subset_closure hc, mem_closedBall_self (by norm_num)⟩
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨c, hcK⟩ (hQc.mono inter_subset_left)
  have hηy := polynomialBallBarrier_unit_mem_Icc hy.2
  have huy := hr.solution_mem_Icc_closure h hy.1
  have huy2 : u y ^ 2 ≤ 1 := by nlinarith [huy.1, huy.2]
  have hQeq {z : Space (m + 1)} (hz : z ∈ epigraph g) :
      Q z = bernsteinQuantity u η A z := by
    simp only [Q, bernsteinQuantity, h.closed_gradient_eq hz]
  have hQbound : Q y ≤ (κ ^ 2 + A * (M + 1)) / 2 := by
    by_cases hyΩ : y ∈ epigraph g
    · by_cases hyball : y ∈ ball c 1
      · have hKnhds : K ∈ 𝓝 y := inter_mem
          (mem_of_superset (hΩ.mem_nhds hyΩ) subset_closure)
          (mem_of_superset (isOpen_ball.mem_nhds hyball) ball_subset_closedBall)
        have hlocal : IsLocalMax (bernsteinQuantity u η A) y :=
          (hmax.isLocalMax hKnhds).congr (by
            filter_upwards [hΩ.mem_nhds hyΩ] with z hz
            exact hQeq hz)
        have hsource := (h.bernstein_weak_laplacian b hη A).nonpos_of_isLocalMax hΩ
          (h.bernsteinQuantity_contDiffOn hη A) (h.bernsteinSource_continuousOn b hη A)
          hyΩ hlocal
        have hlower := h.bernsteinSource_lower_bound b c hB hyΩ hy.2
          (hderiv (u y) ⟨h.positive y hyΩ, huy.2⟩)
        have hfy : 0 ≤ f (u y) := (hr.reaction_pos (u y)
          ⟨h.positive y hyΩ, hr.solution_lt_one y hyΩ⟩).le
        have hfM : f (u y) ≤ M := (le_abs_self _).trans
          (by simpa only [Real.norm_eq_abs] using hreact (u y) huy)
        have huf' : u y * f (u y) ≤ f (u y) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right huy.2 hfy
        have huf : u y * f (u y) ≤ M := huf'.trans hfM
        have hG : ‖gradient u y‖ ^ 2 ≤ A * M := by
          have hm := mul_le_mul_of_nonneg_left huf hA
          change _ ≤ bernsteinSource b u f η A y at hlower
          change ‖gradient u y‖ ^ 2 - A * u y * f (u y) ≤ _ at hlower
          nlinarith only [hlower, hsource, hm]
        have hηG := mul_le_mul_of_nonneg_right hηy.2 (sq_nonneg ‖gradient u y‖)
        have hAu := mul_le_mul_of_nonneg_left huy2 hA
        rw [hQeq hyΩ]
        dsimp only [bernsteinQuantity, η]
        nlinarith [sq_nonneg κ]
      · have hdist : dist y c = 1 := le_antisymm hy.2 (not_lt.mp hyball)
        have hηzero : η y = 0 := polynomialBallBarrier_sphere c y 1 hdist
        have hAu := mul_le_mul_of_nonneg_left huy2 hA
        dsimp only [Q]
        rw [hηzero]
        nlinarith [sq_nonneg κ, mul_nonneg hA hM]
    · have hyle : g (horizontal y) ≤ y (Fin.last m) := by
        simpa only [closure_epigraph h.graph_contDiff.continuous, mem_ofPred_eq] using hy.1
      have hynot : y (Fin.last m) ≤ g (horizontal y) := not_lt.mp hyΩ
      have hypoint : point (horizontal y) (g (horizontal y)) = y := by
        rw [le_antisymm hyle hynot]
        exact point_horizontal_last y
      have huy0 : u y = 0 := by rw [← hypoint, h.dirichlet]
      have hnorm : ‖gradientWithin u (closure (epigraph g)) y‖ ^ 2 = κ ^ 2 := by
        rw [← hypoint, h.boundary_gradient_eq]
        simp only [norm_smul, norm_neg, Real.norm_eq_abs, norm_outwardNormal, mul_one, sq_abs]
      have hηκ := mul_le_mul_of_nonneg_right hηy.2 (sq_nonneg κ)
      dsimp only [Q, η]
      rw [hnorm, huy0]
      nlinarith [mul_nonneg hA (by linarith : 0 ≤ M + 1)]
  have hQcLower : ‖gradient u c‖ ^ 2 / 2 ≤ Q c := by
    rw [hQeq hc]
    dsimp only [bernsteinQuantity, η]
    rw [polynomialBallBarrier_center]
    norm_num
    positivity
  have hh : Q c ≤ Q y := hmax hcK
  change ‖gradient u c‖ ^ 2 ≤ κ ^ 2 + A * (M + 1)
  linarith

/-- The original normalized rigidity hypotheses give a uniform global gradient bound. -/
theorem RigidityHypotheses.exists_global_gradient_sq_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ epigraph g, ‖gradient u x‖ ^ 2 ≤ C := by
  obtain ⟨B, hB, hb⟩ := h.reaction_deriv_bound_on_unit_interval
  obtain ⟨M, hM⟩ := h.reaction_norm_bound_on_unit_interval
  refine ⟨κ ^ 2 + (B + 2 * (m + 1 : ℝ) + 13) * ((M : ℝ) + 1), by positivity, ?_⟩
  exact fun x hx ↦ hr.gradient_sq_le_of_reaction_bounds h (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)
    hB M.coe_nonneg hb hM hx

end SerrinEpigraph
