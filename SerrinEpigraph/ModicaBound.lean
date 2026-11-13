module

public import SerrinEpigraph.GlobalGradientBound
public import SerrinEpigraph.GradientExcessMaximum
public import SerrinEpigraph.QuadraticPenalization

/-!
# The Modica gradient bound under the original rigidity hypotheses

The Bernstein bound controls the excess globally. Quadratic penalization attains
an interior maximum whenever the perturbed excess exceeds its perturbation parameter.
The weak upper-test inequality excludes such a maximum as the penalty tends to zero.
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter Metric
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The continuous excess is zero on the part of the closed epigraph outside its interior. -/
theorem RigidityHypotheses.closedGradientExcess_zero_off_epigraph
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (ε : ℝ)
    {x : Space (m + 1)} (hx : x ∈ closure (epigraph g)) (hn : x ∉ epigraph g) :
    closedGradientExcess g u f ε x = 0 := by
  have hle : g (horizontal x) ≤ x (Fin.last m) := by
    simpa only [closure_epigraph h.graph_contDiff.continuous, mem_ofPred_eq] using hx
  have hge : x (Fin.last m) ≤ g (horizontal x) := not_lt.mp hn
  have he : point (horizontal x) (g (horizontal x)) = x := by
    rw [le_antisymm hle hge]
    exact point_horizontal_last x
  rw [← he]
  exact hr.closedGradientExcess_boundary_zero h ε _

/-- A positive quadratic perturbation bounds the excess everywhere in the epigraph. -/
theorem RigidityHypotheses.gradientExcess_le (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {ε : ℝ} (hε : 0 < ε)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) : gradientExcess u f ε x ≤ ε := by
  by_contra hn
  have hlt : ε < gradientExcess u f ε x := lt_of_not_ge hn
  obtain ⟨C, hC, hCb⟩ := hr.exists_global_gradient_sq_bound h
  obtain ⟨N, hN⟩ := h.reaction_norm_bound_on_unit_interval
  let Q := closedGradientExcess g u f ε
  let δ := gradientExcess u f ε x - ε
  let M := C / 2 + ε + 1
  let D := (N : ℝ) + 2 * ε
  have hδ : 0 < δ := sub_pos.mpr hlt
  have hM : 0 < M := by dsimp only [M]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hQbound : ∀ y ∈ closure (epigraph g), Q y ≤ M := by
    intro y hy
    by_cases hyΩ : y ∈ epigraph g
    · have huy := hr.solution_mem_Icc_closure h hy
      have hW := hr.normalizedPotential_nonneg h huy
      have hu2 : u y ^ 2 ≤ 1 := by nlinarith [huy.1, huy.2]
      have hεu := mul_le_mul_of_nonneg_left hu2 hε.le
      have hg := hCb y hyΩ
      change closedGradientExcess g u f ε y ≤ M
      rw [h.closedGradientExcess_eq ε hyΩ]
      dsimp only [gradientExcess, M]
      nlinarith
    · change closedGradientExcess g u f ε y ≤ M
      rw [hr.closedGradientExcess_zero_off_epigraph h ε hy hyΩ]
      exact hM.le
  have hQboundary : ∀ y ∈ closure (epigraph g), y ∉ epigraph g → Q y ≤ 0 := by
    intro y hy hn
    exact (hr.closedGradientExcess_zero_off_epigraph h ε hy hn).le
  have hQx : 0 < Q x := by
    change 0 < closedGradientExcess g u f ε x
    rw [h.closedGradientExcess_eq ε hx]
    exact hε.trans hlt
  have hineq (t : ℝ) (ht : 0 < t) :
      8 * ε * δ ^ 2 ≤ C * (2 * t ^ 2 * (m + 1 : ℝ)) +
        4 * D * Real.sqrt C * Real.sqrt M * t := by
    obtain ⟨y, hy, hxy, hdist, hlocal⟩ := exists_quadratic_penalized_max hΩ
      (hr.closedGradientExcess_continuousOn h ε) hQbound hQboundary hx hQx (sq_pos_of_pos ht)
    have hlocal' : IsLocalMax (fun z ↦ gradientExcess u f ε z - quadraticPenalty (t ^ 2) x z) y :=
      hlocal.congr (by
        filter_upwards [hΩ.mem_nhds hy] with z hz
        exact congrArg (fun r ↦ r - quadraticPenalty (t ^ 2) x z)
          (h.closedGradientExcess_eq ε hz))
    have htest := hr.gradientExcess_upper_test_inequality h
      (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) hε.le
      (contDiff_quadraticPenalty (t ^ 2) x) hy hlocal'
    rw [laplacian_quadraticPenalty] at htest
    have huy : u y ∈ Icc (0 : ℝ) 1 := hr.solution_mem_Icc_closure h (subset_closure hy)
    have hW := hr.normalizedPotential_nonneg h huy
    have hu2 : u y ^ 2 ≤ 1 := by nlinarith [huy.1, huy.2]
    have hεu := mul_le_mul_of_nonneg_left hu2 hε.le
    have hxy' : gradientExcess u f ε x ≤ gradientExcess u f ε y := by
      change closedGradientExcess g u f ε x ≤ closedGradientExcess g u f ε y at hxy
      simpa only [h.closedGradientExcess_eq ε hx, h.closedGradientExcess_eq ε hy] using hxy
    have hGmin : 2 * δ ≤ ‖gradient u y‖ ^ 2 := by
      dsimp only [δ, gradientExcess] at *
      nlinarith only [hxy', hW, hεu]
    have hGmax : ‖gradient u y‖ ^ 2 ≤ C := hCb y hy
    have hGnorm : ‖gradient u y‖ ≤ Real.sqrt C :=
      (Real.le_sqrt (norm_nonneg _) hC.le).mpr hGmax
    have htr : t * ‖y - x‖ ≤ Real.sqrt M := by
      apply (Real.le_sqrt (mul_nonneg ht.le (norm_nonneg _)) hM.le).mpr
      simpa only [mul_pow] using hdist
    have hqnorm : ‖gradient (quadraticPenalty (t ^ 2) x) y‖ ≤
        2 * t * Real.sqrt M := by
      rw [gradient_quadraticPenalty, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 2 * t ^ 2)]
      nlinarith [mul_le_mul_of_nonneg_left htr (by positivity : 0 ≤ 2 * t)]
    have hcoef0 : 0 ≤ f (u y) + 2 * ε * u y := by
      have hf := hr.reaction_pos (u y) ⟨h.positive y hy, hr.solution_lt_one y hy⟩
      exact add_nonneg hf.le (mul_nonneg (by positivity) huy.1)
    have hcoef : f (u y) + 2 * ε * u y ≤ D := by
      have hf : f (u y) ≤ (N : ℝ) := (le_abs_self _).trans
        (by simpa only [Real.norm_eq_abs] using hN (u y) huy)
      have hh := mul_le_mul_of_nonneg_left huy.2 (by positivity : 0 ≤ 2 * ε)
      dsimp only [D]
      linarith
    have hinner : inner ℝ (gradient u y) (gradient (quadraticPenalty (t ^ 2) x) y) ≤
        Real.sqrt C * (2 * t * Real.sqrt M) :=
      (real_inner_le_norm _ _).trans (mul_le_mul hGnorm hqnorm (norm_nonneg _) (Real.sqrt_nonneg _))
    have hdrift : 2 * (f (u y) + 2 * ε * u y) *
        inner ℝ (gradient u y) (gradient (quadraticPenalty (t ^ 2) x) y) ≤
        4 * D * Real.sqrt C * Real.sqrt M * t := by
      calc
        _ ≤ 2 * (f (u y) + 2 * ε * u y) * (Real.sqrt C * (2 * t * Real.sqrt M)) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ ≤ 2 * D * (Real.sqrt C * (2 * t * Real.sqrt M)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring
    have hlap := mul_le_mul_of_nonneg_right hGmax
      (by positivity : 0 ≤ 2 * t ^ 2 * (m + 1 : ℝ))
    have hpow : (2 * δ) ^ 2 ≤ (‖gradient u y‖ ^ 2) ^ 2 :=
      (sq_le_sq₀ (by positivity) (sq_nonneg _)).mpr hGmin
    have hleft : 8 * ε * δ ^ 2 ≤ 2 * ε * ‖gradient u y‖ ^ 4 := by
      nlinarith only [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * ε)]
    have hq0 := sq_nonneg ‖gradient (quadraticPenalty (t ^ 2) x) y‖
    simp only [Nat.cast_add, Nat.cast_one] at htest
    nlinarith only [hleft, htest, hlap, hdrift, hq0]
  have hlim : Tendsto (fun t : ℝ ↦ C * (2 * t ^ 2 * (m + 1 : ℝ)) +
      4 * D * Real.sqrt C * Real.sqrt M * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ ↦ C * (2 * t ^ 2 * (m + 1 : ℝ)) +
        4 * D * Real.sqrt C * Real.sqrt M * t) := by fun_prop
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, add_zero] using
      (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hzero : 8 * ε * δ ^ 2 ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hineq t ht)
  exact (not_lt_of_ge hzero) (by positivity)

/-- Modica's gradient estimate for the original normalized rigidity hypotheses. -/
theorem RigidityHypotheses.modica_bound (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    ‖gradient u x‖ ^ 2 / 2 ≤ normalizedPotential f (u x) := by
  by_contra hn
  have hpos : 0 < (‖gradient u x‖ ^ 2 / 2 - normalizedPotential f (u x)) / 2 := by
    linarith [lt_of_not_ge hn]
  have hh := hr.gradientExcess_le h hpos hx
  dsimp only [gradientExcess] at hh
  have hp := mul_nonneg hpos.le (sq_nonneg (u x))
  nlinarith

end SerrinEpigraph
