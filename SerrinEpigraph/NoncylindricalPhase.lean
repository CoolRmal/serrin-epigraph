module

public import SerrinEpigraph.HomogeneousPhasePerimeter

/-!
# One-sided cone bounds exclude vertically cylindrical nontrivial phases
-/

public section

open Set MeasureTheory Filter

namespace SerrinEpigraph

/-- A phase above a homogeneous lower cone cannot be invariant under all
vertical translations unless it is null. -/
theorem measure_eq_zero_of_lower_cone_and_vertical_invariance {m : ℕ}
    {E : Set (Space (m + 1))} {C : ℝ}
    (hcone : ∀ᵐ x ∂volume, x ∈ E → -C * ‖horizontal x‖ ≤ x (Fin.last m))
    (htrans : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection m ∈ E) :
    volume E = 0 := by
  have hc (n : ℕ) : ∀ᵐ x ∂volume, x ∈ E →
      -C * ‖horizontal x‖ ≤ x (Fin.last m) - n := by
    have hshift := (measurePreserving_add_right volume
      (-(n : ℝ) • verticalDirection m)).quasiMeasurePreserving.ae hcone
    filter_upwards [htrans (-(n : ℝ)), hshift] with x hx hc
    intro hxE
    have he := hc (hx.mp hxE)
    simpa only [add_vertical_eq_point, horizontal_point, last_point, sub_eq_add_neg] using he
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_all_iff.mpr hc] with x hx
  intro hxE
  obtain ⟨n, hn⟩ := exists_nat_gt (x (Fin.last m) + C * ‖horizontal x‖)
  linarith [hx n hxE]

/-- A phase containing a homogeneous upper cone cannot be invariant under all
vertical translations unless its complement is null. -/
theorem measure_compl_eq_zero_of_upper_cone_and_vertical_invariance {m : ℕ}
    {E : Set (Space (m + 1))} {C : ℝ}
    (hcone : ∀ᵐ x ∂volume, C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E)
    (htrans : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection m ∈ E) :
    volume Eᶜ = 0 := by
  have hc (n : ℕ) : ∀ᵐ x ∂volume,
      C * ‖horizontal x‖ < x (Fin.last m) + n → x ∈ E := by
    have hshift := (measurePreserving_add_right volume
      ((n : ℝ) • verticalDirection m)).quasiMeasurePreserving.ae hcone
    filter_upwards [htrans (n : ℝ), hshift] with x hx hc
    intro habove
    apply hx.mpr
    apply hc
    simpa only [add_vertical_eq_point, horizontal_point, last_point] using habove
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_all_iff.mpr hc] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (C * ‖horizontal x‖ - x (Fin.last m))
  exact fun hxE ↦ hxE (hx n (by linarith))

/-- Either one-sided cone constraint rules out the vertically cylindrical
alternative for a phase whose two sides both have positive measure. -/
theorem not_vertical_invariant_of_nontrivial_oneSided_cone {m : ℕ}
    {E : Set (Space (m + 1))} (hne : volume E ≠ 0 ∧ volume Eᶜ ≠ 0)
    (hcone : (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
      x ∈ E → -C * ‖horizontal x‖ ≤ x (Fin.last m)) ∨
      (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
        C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E)) :
    ¬(∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection m ∈ E) := by
  intro htrans
  rcases hcone with ⟨C, _, hc⟩ | ⟨C, _, hc⟩
  · exact hne.1 (measure_eq_zero_of_lower_cone_and_vertical_invariance hc htrans)
  · exact hne.2 (measure_compl_eq_zero_of_upper_cone_and_vertical_invariance hc htrans)

end SerrinEpigraph
