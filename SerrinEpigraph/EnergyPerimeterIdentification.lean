module

public import SerrinEpigraph.RecoveryEnergyUpper

/-!
# Identification of homogeneous diffuse-energy mass with phase perimeter
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Recovery of the limiting phase bounds every smaller-ball energy limit by
the phase's perimeter bound on a larger ball. -/
theorem RigidityHypotheses.energy_limit_le_perimeter_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {a s B L : ℝ} (ha : 0 < a) (has : a < s) (hB : 0 ≤ B)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hP : variationalPerimeter basis E (ball 0 s) ≤ ENNReal.ofReal B)
    (henergy : Tendsto (fun j ↦ ∫ x in closedBall 0 a,
      rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x)
        atTop (𝓝 L)) : L ≤ phasePrimitive f 1 * B := by
  let r := (a + s) / 2
  let t := (s - r) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have har : a < r := by dsimp [r]; linarith
  have ht : 0 < t := by dsimp [t, r]; linarith
  have hrts : r + t < s := by dsimp [t, r]; linarith
  have hsmall : closedBall (0 : Space (m + 1)) (r + t) ⊆ closedBall 0 s :=
    closedBall_subset_closedBall hrts.le
  have hU (j : ℕ) : LocallyLipschitz (fun y ↦ zeroExtension g u (R j • y)) :=
    h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
  have hUval (j : ℕ) (x : Space (m + 1)) : zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hiE : IntegrableOn (E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ)))
      (closedBall 0 s) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _)).indicator hE
  have hlim := integral_norm_sub_tendsto_of_subset hsmall
    (fun j ↦ (((hU j).continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).sub hiE).norm) hUlim
  obtain ⟨n, v, D, _, hnt, hv, hval, hvlim, hbound, hDt⟩ :=
    hr.exists_finitePerimeter_recovery h basis hE hrts hB hP R
      (fun j ↦ zero_lt_one.trans_le (hR j)) hRt
  obtain ⟨ε, hεt, hcomp⟩ := hr.exists_inner_energy_recovery_error h hr0 ht
    (fun j ↦ hR (n j)) (hRt.comp hnt) hv hval hE (hlim.comp hnt) hvlim hbound hDt
  have hclosed (j : ℕ) : (∫ x in closedBall 0 a,
      rescaledPhaseEnergyDensity f (R (n j)) (fun y ↦ zeroExtension g u (R (n j) • y)) x) ≤
        D j + ε j := by
    have hi := (h.integrableOn_rescaledPhaseEnergy (hU (n j)) (hUval (n j)) (R (n j))
      (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
    have he := setIntegral_mono_set hi
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h
        (zero_lt_one.trans_le (hR (n j))).le (hUval (n j))))
      (Eventually.of_forall (closedBall_subset_ball har))
    exact he.trans (hcomp j)
  simpa only [add_zero] using le_of_tendsto_of_tendsto (henergy.comp hnt) (hDt.add hεt)
    (Eventually.of_forall hclosed)

/-- The homogeneous ball-energy limit equals the interface constant times
the perimeter of any local phase limit, with no loss of variation on these balls. -/
theorem RigidityHypotheses.phase_perimeter_eq_energy_mass
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {L : ℝ} (henergy : ∀ a : ℝ, 0 < a →
      Tendsto (fun T : ℝ ↦ ∫ x in closedBall 0 a,
        rescaledPhaseEnergyDensity f T (fun y ↦ zeroExtension g u (T • y)) x)
          atTop (𝓝 (a ^ m * L)))
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (phasePrimitive f 1) * variationalPerimeter basis E (ball 0 s) =
      ENNReal.ofReal (s ^ m * L) := by
  have hc : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  have hU (j : ℕ) : LocallyLipschitz (fun y ↦ zeroExtension g u (R j • y)) :=
    h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
  have hUval (j : ℕ) (x : Space (m + 1)) : zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hprim := hr.competitorPrimitive_integral_limit h hU hUval hE
    (isCompact_closedBall 0 s) (hlocal _ (isCompact_closedBall _ _))
  have hupper := hr.perimeter_le_energy_liminf h basis R
    (fun j ↦ zero_lt_one.trans_le (hR j)) s hE hprim
  have hmass := (ENNReal.tendsto_ofReal ((henergy s hs).comp hRt)).liminf_eq
  simp only [Function.comp_def] at hmass
  rw [hmass] at hupper
  apply le_antisymm hupper
  by_cases htop : variationalPerimeter basis E (ball 0 s) = ⊤
  · simp [htop, (ENNReal.ofReal_pos.mpr hc).ne']
  have hP : variationalPerimeter basis E (ball 0 s) ≤
      ENNReal.ofReal (variationalPerimeter basis E (ball 0 s)).toReal := by
    rw [ENNReal.ofReal_toReal htop]
  have hinner (a : ℝ) (ha : a ∈ Ioo 0 s) :
      a ^ m * L ≤ phasePrimitive f 1 * (variationalPerimeter basis E (ball 0 s)).toReal :=
    hr.energy_limit_le_perimeter_bound h basis ha.1 ha.2 ENNReal.toReal_nonneg hR hRt hE
      (hlocal _ (isCompact_closedBall _ _)) hP ((henergy a ha.1).comp hRt)
  let : NeBot (𝓝[Ioo 0 s] s) := right_nhdsWithin_Ioo_neBot hs
  have ht : Tendsto (fun a : ℝ ↦ a ^ m * L) (𝓝[Ioo 0 s] s) (𝓝 (s ^ m * L)) :=
    ((continuous_id.pow m).mul continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hl := le_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact hinner a ha)
  have he := ENNReal.ofReal_le_ofReal hl
  rwa [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal htop] at he

end SerrinEpigraph
