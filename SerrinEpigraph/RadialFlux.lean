module

public import SerrinEpigraph.RadialEnergy

/-!
# Radial flux and monotonicity of ball profiles
-/

public section
noncomputable section

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Multiplication by the radial volume weight removes the singular drift term. -/
theorem Hypotheses.radialFlux_hasDerivAt (h : Hypotheses g u f κ)
    {q p : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hp : HasDerivAt p (-f (q r) - (m : ℝ) / r * p r) r) :
    HasDerivAt (fun t ↦ t ^ m * p t) (-(r ^ m * f (q r))) r := by
  have hm : m ≠ 0 := by have hd := h.dimension; omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have he := (hasDerivAt_pow (k + 1) r).mul hp
  convert he using 1
  simp only [Nat.add_sub_cancel, Nat.cast_succ, pow_succ]
  field_simp [hr.ne']
  ring

/-- The weighted radial flux is nonincreasing throughout the closed radius interval. -/
theorem RadialBallProfile.flux_antitoneOn {R : ℝ} (v : RadialBallProfile f m R)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    AntitoneOn (fun r ↦ r ^ m * v.slope r) (Set.Icc 0 R) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) R)
    ((continuousOn_id.pow m).mul v.slope_continuous)
    (f' := fun r ↦ -(r ^ m * f (v.value r)))
  · intro r hr'
    have hr'' : r ∈ Set.Ioo (0 : ℝ) R := by simpa only [interior_Icc] using hr'
    exact (h.radialFlux_hasDerivAt hr''.1 (v.slope_derivative r hr'')).hasDerivWithinAt
  · intro r hr'
    have hr'' : r ∈ Set.Ioo (0 : ℝ) R := by simpa only [interior_Icc] using hr'
    have hv := v.value_range r ⟨hr''.1.le, hr''.2.le⟩
    have hf : 0 ≤ f (v.value r) := by
      rcases lt_or_eq_of_le hv.2 with hlt | he
      · exact (hr.reaction_pos _ ⟨v.value_pos r hr'', hlt⟩).le
      · rw [he, hr.reaction_one]
    exact neg_nonpos.mpr (mul_nonneg (pow_nonneg hr''.1.le _) hf)

/-- Radial ball profiles have nonpositive slope, including both endpoints. -/
theorem RadialBallProfile.slope_nonpos {R : ℝ} (v : RadialBallProfile f m R)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {r : ℝ} (hr' : r ∈ Set.Icc 0 R) : v.slope r ≤ 0 := by
  by_cases hz : r = 0
  · simp only [hz, v.slope_zero, le_refl]
  · have hp : 0 < r := lt_of_le_of_ne hr'.1 (Ne.symm hz)
    have he := v.flux_antitoneOn hr h ⟨le_rfl, v.radius_pos.le⟩ hr' hr'.1
    simp only [v.slope_zero, mul_zero] at he
    exact nonpos_of_mul_nonpos_right he (pow_pos hp _)

/-- The values of a radial ball profile decrease from the center toward the boundary. -/
theorem RadialBallProfile.value_antitoneOn {R : ℝ} (v : RadialBallProfile f m R)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    AntitoneOn v.value (Set.Icc 0 R) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) R) v.value_continuous
    (f' := v.slope)
  · intro r hr'
    exact (v.value_derivative r (by simpa only [interior_Icc] using hr')).hasDerivWithinAt
  · intro r hr'
    have hi : r ∈ Set.Ioo (0 : ℝ) R := by simpa only [interior_Icc] using hr'
    exact v.slope_nonpos hr h ⟨hi.1.le, hi.2.le⟩

/-- The central value is positive, as follows from positivity away from the center and monotonicity. -/
theorem RadialBallProfile.value_zero_pos {R : ℝ} (v : RadialBallProfile f m R)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) : 0 < v.value 0 := by
  have hp : R / 2 ∈ Set.Ioo (0 : ℝ) R := ⟨half_pos v.radius_pos, half_lt_self v.radius_pos⟩
  exact (v.value_pos _ hp).trans_le (v.value_antitoneOn hr h
    ⟨le_rfl, v.radius_pos.le⟩ ⟨hp.1.le, hp.2.le⟩ hp.1.le)

/-- The radial boundary slope is strictly negative. -/
theorem RadialBallProfile.boundary_slope_neg {R : ℝ} (v : RadialBallProfile f m R)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) : v.slope R < 0 := by
  obtain ⟨r, hr', he⟩ := exists_hasDerivAt_eq_slope v.value v.slope v.radius_pos
    v.value_continuous v.value_derivative
  have hp : v.slope r < 0 := by
    rw [he, v.boundary_zero, zero_sub, sub_zero]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (v.value_zero_pos hr h)) v.radius_pos
  have hf := v.flux_antitoneOn hr h ⟨hr'.1.le, hr'.2.le⟩ ⟨v.radius_pos.le, le_rfl⟩ hr'.2.le
  have hn : r ^ m * v.slope r < 0 := mul_neg_of_pos_of_neg (pow_pos hr'.1 _) hp
  exact neg_of_mul_neg_right (hf.trans_lt hn) (pow_nonneg v.radius_pos.le _)

/-- The weighted slope is the negative integrated radial reaction, with the center included. -/
theorem RadialBallProfile.flux_eq_integral {R : ℝ} (v : RadialBallProfile f m R)
    (h : Hypotheses g u f κ) {r : ℝ} (hr : r ∈ Set.Icc 0 R) :
    r ^ m * v.slope r = -(∫ t in (0 : ℝ)..r, t ^ m * f (v.value t)) := by
  have hsub : Set.Icc (0 : ℝ) r ⊆ Set.Icc (0 : ℝ) R :=
    Set.Icc_subset_Icc_right hr.2
  have hc := ((continuousOn_id.pow m).mul v.slope_continuous).mono hsub
  have hreact : ContinuousOn (fun t ↦ f (v.value t)) (Set.Icc (0 : ℝ) r) :=
    h.reaction_contDiffOn.continuousOn.comp (v.value_continuous.mono hsub)
      (fun t ht ↦ (v.value_range t (hsub ht)).1)
  have hi := (((continuousOn_id.pow m).mul hreact).neg).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hr.1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 hc
    (fun t ht ↦ h.radialFlux_hasDerivAt ht.1
      (v.slope_derivative t ⟨ht.1, ht.2.trans_le hr.2⟩)) hi
  simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, intervalIntegral.integral_neg,
    v.slope_zero, mul_zero, sub_zero] using he.symm

end SerrinEpigraph
