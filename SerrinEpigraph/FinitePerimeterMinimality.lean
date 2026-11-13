module

public import SerrinEpigraph.FinitePerimeterRecovery

/-!
# Perimeter minimality against arbitrary measurable competitors
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- General finite-perimeter recovery and annular gluing bound the limiting
phase's interior perimeter by a measurable competitor's larger-ball perimeter. -/
theorem RigidityHypotheses.limiting_perimeter_le_measurable_competitor
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {r t a s : ℝ} (hradius : 0 < r) (ht : 0 < t) (har : a < r) (hrts : r + t < s)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E D : Set (Space (m + 1))} (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t),
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hagree : ∀ x ∈ closedBall 0 (r + t) \ ball 0 r, x ∈ E ↔ x ∈ D) :
    variationalPerimeter basis E (ball 0 a) ≤ variationalPerimeter basis D (ball 0 s) := by
  by_cases htop : variationalPerimeter basis D (ball 0 s) = ⊤
  · rw [htop]
    exact le_top
  have hP : variationalPerimeter basis D (ball 0 s) ≤
      ENNReal.ofReal (variationalPerimeter basis D (ball 0 s)).toReal := by
    rw [ENNReal.ofReal_toReal htop]
  obtain ⟨n, v, B, _, hnt, hv, hval, hvlim, hbound, hBt⟩ :=
    hr.exists_finitePerimeter_recovery h basis hD hrts ENNReal.toReal_nonneg hP R
      (fun j ↦ zero_lt_one.trans_le (hR j)) hRt
  have he := hr.perimeter_le_recovery_bound_of_annular_agreement h basis hradius ht har
    (fun j ↦ hR (n j)) (hRt.comp hnt) hv hval hE hD hagree (hUlim.comp hnt)
    hvlim hbound hBt
  have hc : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal htop] at he
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hc).ne'
    ENNReal.ofReal_ne_top).mp he

/-- A fixed local phase limit minimizes perimeter against every measurable
competitor agreeing with it outside a strictly smaller concentric closed ball. -/
theorem RigidityHypotheses.limiting_phase_perimeter_minimality
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {s r₀ : ℝ} (hs : 0 < s) (hr₀ : r₀ < s)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E D : Set (Space (m + 1))} (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hagree : ∀ x ∈ ball 0 s \ closedBall 0 r₀, x ∈ E ↔ x ∈ D) :
    variationalPerimeter basis E (ball 0 s) ≤ variationalPerimeter basis D (ball 0 s) := by
  unfold variationalPerimeter at ⊢
  refine iSup_le (fun F ↦ iSup_le (fun hF ↦ iSup_le (fun hc ↦
    iSup_le (fun hFs ↦ iSup_le (fun hunit ↦ ?_)))))
  obtain ⟨a, has, hFa⟩ := exists_lt_subset_ball (isClosed_tsupport F) hFs
  obtain ⟨r, hlow, hrs⟩ := exists_between (max_lt has (max_lt hs hr₀))
  have har : a < r := (le_max_left _ _).trans_lt hlow
  have hrpos : 0 < r := (le_max_left 0 r₀).trans (le_max_right a (max 0 r₀)) |>.trans_lt hlow
  have hr₀r : r₀ < r := (le_max_right 0 r₀).trans (le_max_right a (max 0 r₀)) |>.trans_lt hlow
  let t := (s - r) / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hrts : r + t < s := by dsimp [t]; linarith
  have hsmall : closedBall (0 : Space (m + 1)) (r + t) ⊆ ball 0 s :=
    closedBall_subset_ball hrts
  have hiE : IntegrableOn (E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ)))
      (closedBall 0 s) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _)).indicator hE
  have hlim := integral_norm_sub_tendsto_of_subset (hsmall.trans ball_subset_closedBall)
    (fun j ↦ (((h.zeroExtension_continuous.comp
      (continuous_id.const_smul (R j))).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).sub hiE).norm) hUlim
  have hcomp := hr.limiting_perimeter_le_measurable_competitor h basis hrpos ht har hrts
    hR hRt hE hD hlim (fun x hx ↦ hagree x ⟨hsmall hx.1, fun hx₀ ↦ hx.2
      (closedBall_subset_ball hr₀r hx₀)⟩)
  apply le_trans _ hcomp
  unfold variationalPerimeter
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hc
    (le_iSup_of_le hFa (le_iSup_of_le hunit le_rfl))))

/-- Full measurable-competitor minimality is unchanged by null-set differences
in the required outer-annulus agreement. -/
theorem RigidityHypotheses.limiting_phase_perimeter_minimality_ae
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {s r₀ : ℝ} (hs : 0 < s) (hr₀ : r₀ < s)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E D : Set (Space (m + 1))} (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hagree : ∀ᵐ x ∂volume.restrict (ball 0 s \ closedBall 0 r₀), x ∈ E ↔ x ∈ D) :
    variationalPerimeter basis E (ball 0 s) ≤ variationalPerimeter basis D (ball 0 s) := by
  let A := ball (0 : Space (m + 1)) s \ closedBall 0 r₀
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  let E' := (E \ A) ∪ (D ∩ A)
  have hE' : MeasurableSet E' := (hE.diff hA).union (hD.inter hA)
  have hEE' : E =ᵐ[volume] E' := by
    have ha : ∀ᵐ x ∂volume, x ∈ A → (x ∈ E ↔ x ∈ D) := (ae_restrict_iff' hA).mp hagree
    filter_upwards [ha] with x hx
    apply propext
    by_cases hxA : x ∈ A
    · simpa only [E', mem_union, Set.mem_sdiff, mem_inter_iff, hxA, not_true_eq_false,
        and_false, and_true, false_or] using hx hxA
    · simp only [E', mem_union, Set.mem_sdiff, mem_inter_iff, hxA, not_false_eq_true,
        and_true, and_false, or_false]
  have hlimE' : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (R j • x) - E'.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
    convert hUlim using 1
    funext j
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (phaseIndicator_congr_ae hEE')] with x hx
    rw [hx]
  rw [variationalPerimeter_congr_ae basis hEE']
  apply hr.limiting_phase_perimeter_minimality h basis hs hr₀ hR hRt hE' hD hlimE'
  intro x hx
  have hxA : x ∈ A := hx
  simp only [E', mem_union, Set.mem_sdiff, mem_inter_iff, hxA, not_true_eq_false,
    and_false, and_true, false_or]

end SerrinEpigraph
