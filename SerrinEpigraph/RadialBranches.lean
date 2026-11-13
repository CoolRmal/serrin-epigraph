module

public import SerrinEpigraph.RadialUnion

/-!
# Positive radial branches extending a fixed central solution
-/

public section
noncomputable section
open Set

namespace SerrinEpigraph

/-- A normalized positive radial solution on a half-open central interval. -/
structure RadialBranch (f : ℝ → ℝ) (m : ℕ) (a : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  value : ℝ → ℝ
  slope : ℝ → ℝ
  value_continuous : ContinuousOn value (Ico 0 radius)
  slope_continuous : ContinuousOn slope (Ico 0 radius)
  value_range : ∀ t ∈ Ico (0 : ℝ) radius, value t ∈ Ioo (0 : ℝ) 1
  value_zero : value 0 = a
  slope_zero : slope 0 = 0
  system : IsRadialSystemOn m f value slope (Ioo 0 radius)

/-- A radial branch extending all the values and slopes of a fixed seed branch. -/
structure RadialExtension {f : ℝ → ℝ} {m : ℕ} {a : ℝ} (seed : RadialBranch f m a) where
  branch : RadialBranch f m a
  radius_ge : seed.radius ≤ branch.radius
  value_eq : EqOn branch.value seed.value (Ico 0 seed.radius)
  slope_eq : EqOn branch.slope seed.slope (Ico 0 seed.radius)

/-- Every seed is itself an extension, so its family of extensions is nonempty. -/
@[expose] def RadialBranch.selfExtension {f : ℝ → ℝ} {m : ℕ} {a : ℝ}
    (seed : RadialBranch f m a) : RadialExtension seed where
  branch := seed
  radius_ge := le_rfl
  value_eq := fun _ _ ↦ rfl
  slope_eq := fun _ _ ↦ rfl

instance {f : ℝ → ℝ} {m : ℕ} {a : ℝ} (seed : RadialBranch f m a) :
    Nonempty (RadialExtension seed) := ⟨seed.selfExtension⟩

/-- The original reaction assumptions provide a seed for each normalized central value. -/
theorem Hypotheses.nonempty_radialBranch
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a : ℝ}
    (h : Hypotheses g u f κ) (ha : a ∈ Ioo (0 : ℝ) 1) : Nonempty (RadialBranch f m a) := by
  obtain ⟨R, hR, Q, P, hQc, hPc, hQ0, hP0, hval, hQd, hPd⟩ :=
    h.exists_local_radial_system ha
  exact ⟨{
    radius := R
    radius_pos := hR
    value := Q
    slope := P
    value_continuous := hQc.continuousOn
    slope_continuous := hPc.mono Ico_subset_Icc_self
    value_range := fun t ht ↦ hval t ⟨ht.1, ht.2.le⟩
    value_zero := hQ0
    slope_zero := hP0
    system := fun t ht ↦ ⟨hQd t ⟨ht.1.le, ht.2.le⟩, hPd t ht⟩
  }⟩

/-- Any two extensions of the same seed agree on their full common central interval. -/
theorem RadialExtension.compatible
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a : ℝ}
    (h : Hypotheses g u f κ) {seed : RadialBranch f m a}
    (v w : RadialExtension seed) :
    EqOn v.branch.value w.branch.value
      (Ico 0 v.branch.radius ∩ Ico 0 w.branch.radius) ∧
    EqOn v.branch.slope w.branch.slope
      (Ico 0 v.branch.radius ∩ Ico 0 w.branch.radius) := by
  let S := Ioo (0 : ℝ) (min v.branch.radius w.branch.radius)
  have hseed : seed.radius / 2 ∈ Ico (0 : ℝ) seed.radius :=
    ⟨by have := seed.radius_pos; positivity, by have := seed.radius_pos; linarith⟩
  have hmid : seed.radius / 2 ∈ S := by
    refine ⟨by have := seed.radius_pos; positivity, lt_min ?_ ?_⟩
    · exact hseed.2.trans_le v.radius_ge
    · exact hseed.2.trans_le w.radius_ge
  have hvS : S ⊆ Ioo (0 : ℝ) v.branch.radius :=
    fun _ ht ↦ ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hwS : S ⊆ Ioo (0 : ℝ) w.branch.radius :=
    fun _ ht ↦ ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
  obtain ⟨hQ, hP⟩ := h.radial_system_eqOn isOpen_Ioo
    (convex_Ioo (0 : ℝ) (min v.branch.radius w.branch.radius)).isPreconnected hmid
    (fun t ht ↦ ⟨ht.1, (v.branch.value_range t ⟨ht.1.le, (hvS ht).2⟩).1⟩)
    (fun t ht ↦ (v.branch.system t (hvS ht)).1)
    (fun t ht ↦ (v.branch.system t (hvS ht)).2)
    (fun t ht ↦ (w.branch.system t (hwS ht)).1)
    (fun t ht ↦ (w.branch.system t (hwS ht)).2)
    ((v.value_eq hseed).trans (w.value_eq hseed).symm)
    ((v.slope_eq hseed).trans (w.slope_eq hseed).symm)
  constructor
  · intro t ht
    by_cases hz : t = 0
    · simp [hz, v.branch.value_zero, w.branch.value_zero]
    · exact hQ ⟨lt_of_le_of_ne ht.1.1 (Ne.symm hz), lt_min ht.1.2 ht.2.2⟩
  · intro t ht
    by_cases hz : t = 0
    · simp [hz, v.branch.slope_zero, w.branch.slope_zero]
    · exact hP ⟨lt_of_le_of_ne ht.1.1 (Ne.symm hz), lt_min ht.1.2 ht.2.2⟩

/-- Bounded extension radii have a positive supremum at least as large as the seed radius. -/
theorem RadialBranch.le_extension_radius_sup {f : ℝ → ℝ} {m : ℕ} {a : ℝ}
    (seed : RadialBranch f m a)
    (hb : BddAbove (range (fun v : RadialExtension seed ↦ v.branch.radius))) :
    seed.radius ≤ sSup (range (fun v : RadialExtension seed ↦ v.branch.radius)) :=
  le_csSup hb (mem_range.mpr ⟨seed.selfExtension, rfl⟩)

/-- The union of all bounded extensions is itself an extension at the supremal radius. -/
@[expose] def RadialBranch.supExtension
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a : ℝ}
    (h : Hypotheses g u f κ) (seed : RadialBranch f m a)
    (hb : BddAbove (range (fun v : RadialExtension seed ↦ v.branch.radius))) :
    RadialExtension seed := by
  let R := fun v : RadialExtension seed ↦ v.branch.radius
  let Q := fun v : RadialExtension seed ↦ v.branch.value
  let P := fun v : RadialExtension seed ↦ v.branch.slope
  have hQ := fun v w : RadialExtension seed ↦ (v.compatible h w).1
  have hP := fun v w : RadialExtension seed ↦ (v.compatible h w).2
  have hd := radialUnion_domain_eq_Ico hb
  have hdi := radialUnion_positive_domain_eq_Ioo hb
  have hQc : ContinuousOn (radialUnion R Q) (Ico 0 (sSup (range R))) := by
    rw [← hd]
    exact radialUnion_continuousOn hQ (fun v ↦ v.branch.value_continuous)
  have hPc : ContinuousOn (radialUnion R P) (Ico 0 (sSup (range R))) := by
    rw [← hd]
    exact radialUnion_continuousOn hP (fun v ↦ v.branch.slope_continuous)
  have hval : ∀ t ∈ Ico (0 : ℝ) (sSup (range R)), radialUnion R Q t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht
    apply radialUnion_mem_Ioo hQ (fun v ↦ v.branch.value_range)
    rwa [hd]
  have hsys : IsRadialSystemOn m f (radialUnion R Q) (radialUnion R P)
      (Ioo 0 (sSup (range R))) := by
    rw [← hdi]
    exact radialUnion_isRadialSystemOn hQ hP (fun v ↦ v.branch.system)
  exact {
    branch := {
      radius := sSup (range R)
      radius_pos := seed.radius_pos.trans_le (seed.le_extension_radius_sup hb)
      value := radialUnion R Q
      slope := radialUnion R P
      value_continuous := hQc
      slope_continuous := hPc
      value_range := hval
      value_zero := radialUnion_center hQ seed.selfExtension seed.radius_pos seed.value_zero
      slope_zero := radialUnion_center hP seed.selfExtension seed.radius_pos seed.slope_zero
      system := hsys
    }
    radius_ge := seed.le_extension_radius_sup hb
    value_eq := radialUnion_eqOn hQ seed.selfExtension
    slope_eq := radialUnion_eqOn hP seed.selfExtension
  }

/-- If all extension radii are bounded, their supremum yields a Dirichlet ball solution. -/
theorem RadialBranch.exists_ballProfile_of_bdd_extensions
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (seed : RadialBranch f m a)
    (hb : BddAbove (range (fun v : RadialExtension seed ↦ v.branch.radius))) :
    ∃ R : ℝ, seed.radius ≤ R ∧ ∃ v : RadialBallProfile f m R,
      EqOn v.value seed.value (Ico 0 seed.radius) ∧
      EqOn v.slope seed.slope (Ico 0 seed.radius) := by
  let v := seed.supExtension h hb
  have hsup : v.branch.radius =
      sSup (range (fun e : RadialExtension seed ↦ e.branch.radius)) := rfl
  rcases hr.radial_ballProfile_or_extension h v.branch.radius_pos
    v.branch.value_continuous v.branch.slope_continuous v.branch.system
    v.branch.value_range v.branch.slope_zero with hball | hext
  · obtain ⟨w, hwQ, hwP, _, _⟩ := hball
    refine ⟨v.branch.radius, v.radius_ge, w, ?_, ?_⟩
    · intro t ht
      exact (hwQ ⟨ht.1, ht.2.trans_le v.radius_ge⟩).trans (v.value_eq ht)
    · intro t ht
      exact (hwP ⟨ht.1, ht.2.trans_le v.radius_ge⟩).trans (v.slope_eq ht)
  · obtain ⟨ε, hε, W, Z, hsys, hWc, hZc, hWQ, hZP, hval⟩ := hext
    have hzero : (0 : ℝ) ∈ Ico 0 v.branch.radius := ⟨le_rfl, v.branch.radius_pos⟩
    let e : RadialExtension seed := {
      branch := {
        radius := v.branch.radius + ε
        radius_pos := by linarith [v.branch.radius_pos]
        value := W
        slope := Z
        value_continuous := hWc
        slope_continuous := hZc
        value_range := by
          intro t ht
          rcases eq_or_lt_of_le ht.1 with hz | hpos
          · subst t
            rw [hWQ hzero]
            exact v.branch.value_range 0 hzero
          · exact hval t ⟨hpos, ht.2⟩
        value_zero := (hWQ hzero).trans v.branch.value_zero
        slope_zero := (hZP hzero).trans v.branch.slope_zero
        system := hsys
      }
      radius_ge := by linarith [v.radius_ge]
      value_eq := fun t ht ↦ (hWQ ⟨ht.1, ht.2.trans_le v.radius_ge⟩).trans (v.value_eq ht)
      slope_eq := fun t ht ↦ (hZP ⟨ht.1, ht.2.trans_le v.radius_ge⟩).trans (v.slope_eq ht)
    }
    have he := le_csSup hb (mem_range_self e)
    change v.branch.radius + ε ≤ _ at he
    rw [← hsup] at he
    linarith

end SerrinEpigraph
