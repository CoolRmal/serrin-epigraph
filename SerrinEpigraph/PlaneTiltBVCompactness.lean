module

public import SerrinEpigraph.PlaneTiltTranslatedEnergy
public import SerrinEpigraph.SimultaneousMollifiedCompactness
public import SerrinEpigraph.GlobalPrimitiveLimit

/-!
# Local integral compactness from uniform gradient mass
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology BoundedContinuousFunction

namespace SerrinEpigraph

/-- A local gradient-mass bound gives an explicit integral mollification error. -/
theorem integral_mollify_error_le_gradient_mass {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) (n : ℕ) {r C : ℝ} (hC : 0 ≤ C)
    (hbound : (∫ x in closedBall 0 (r + 1), ‖gradient v x‖) ≤ C) :
    (∫ x in closedBall 0 r, ‖mollify v n x - v x‖) ≤ (1 / ((n : ℝ) + 1)) * C := by
  apply integral_norm_mollify_sub_le hv.continuous n r
  intro t ht
  have htρ : ‖t‖ ≤ 1 / ((n : ℝ) + 1) :=
    (show ‖t‖ < (averagingBump d n).rOut by simpa using ht).le
  have ht1 : ‖t‖ ≤ 1 := htρ.trans (averagingBump_rOut_le_one d n)
  have hi := integral_norm_translate_sub_le_of_locallyLipschitz hv r (-t)
  simp only [norm_neg, ← sub_eq_add_neg] at hi
  apply hi.trans
  have hm : (∫ x in closedBall 0 (r + ‖t‖), ‖gradient v x‖) ≤ C := by
    apply le_trans _ hbound
    exact setIntegral_mono_set
      (integrableOn_gradient_of_locallyLipschitz hv (isCompact_closedBall 0 (r + 1))).norm
      (Eventually.of_forall (fun x ↦ norm_nonneg _))
      (Eventually.of_forall (closedBall_subset_closedBall (by linarith)))
  exact (mul_le_mul_of_nonneg_left hm (norm_nonneg t)).trans
    (mul_le_mul_of_nonneg_right htρ hC)

/-- Every countable family of mollifications of bounded continuous functions admits
one common uniformly convergent subsequence on all integer balls. -/
theorem exists_simultaneous_mollified_subsequence {d : ℕ}
    (F : ℕ → Space d → ℝ) (hF : ∀ j, Continuous (F j)) {M : ℝ}
    (hval : ∀ j x, F j x ∈ Icc (0 : ℝ) M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n k : ℕ,
      ∃ v : (closedBall (0 : Space d) (k + 1 : ℝ)) →ᵇ ℝ,
        TendstoUniformly (fun j (x : closedBall (0 : Space d) (k + 1 : ℝ)) ↦
          mollify (F (φ j)) n x) v atTop := by
  have hM : 0 ≤ M := (hval 0 0).1.trans (hval 0 0).2
  let X (i : ℕ × ℕ) := closedBall (0 : Space d) (i.2 + 1 : ℝ)
  let : ∀ i, CompactSpace (X i) := fun i ↦
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space d) (i.2 + 1 : ℝ))
  let G : ∀ i : ℕ × ℕ, ℕ → X i →ᵇ ℝ := fun i j ↦
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x ↦ mollify (F j) i.1 x,
        (mollify_contDiff (hF j) i.1).continuous.comp continuous_subtype_val⟩
  have hC (i : ℕ × ℕ) := mollify_family_lipschitzOn (d := d) i.1 (i.2 + 1 : ℝ) M hM
  choose C hC using hC
  have hCG (i : ℕ × ℕ) (j : ℕ) : LipschitzWith (C i) (G i j) := by
    exact (hC i (F j) (hF j) (fun x ↦ by
      rw [Real.norm_of_nonneg (hval j x).1]; exact (hval j x).2)).to_restrict
  have hMG (i : ℕ × ℕ) (j : ℕ) (x : X i) : G i j x ∈ Icc (0 : ℝ) M :=
    ⟨mollify_nonneg (fun y ↦ (hval j y).1) i.1 x,
      mollify_le (hF j) (fun y ↦ (hval j y).2) i.1 x⟩
  obtain ⟨φ, hφ, hv⟩ := exists_simultaneous_uniform_subsequence G C (fun _ ↦ M) hCG hMG
  exact ⟨φ, hφ, fun n k ↦ hv (n, k)⟩

/-- Bounded locally Lipschitz functions with uniformly bounded local gradient mass
have a common local integral limit on the whole space. -/
theorem exists_local_integral_subsequence_of_gradient_mass {d : ℕ}
    (F : ℕ → Space d → ℝ) (hF : ∀ j, LocallyLipschitz (F j)) {M : ℝ}
    (hval : ∀ j x, F j x ∈ Icc (0 : ℝ) M) (C : ℕ → ℝ)
    (hbound : ∀ j k : ℕ, (∫ x in closedBall 0 (k + 2 : ℝ), ‖gradient (F j) x‖) ≤ C k) :
    ∃ (φ : ℕ → ℕ) (v : Space d → ℝ), StrictMono φ ∧
      ∀ K : Set (Space d), IsCompact K → IntegrableOn v K ∧
        Tendsto (fun j ↦ ∫ x in K, ‖F (φ j) x - v x‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hlim⟩ := exists_simultaneous_mollified_subsequence F
    (fun j ↦ (hF j).continuous) hval
  have hC (k : ℕ) : 0 ≤ C k :=
    (integral_nonneg (fun x ↦ norm_nonneg (gradient (F 0) x))).trans (hbound 0 k)
  have hFi (j : ℕ) (k : ℕ) : IntegrableOn (F (φ j)) (closedBall 0 (k + 1 : ℝ)) :=
    (hF (φ j)).continuous.continuousOn.integrableOn_compact (isCompact_closedBall 0 _)
  have hc (k : ℕ) : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N,
      (∫ x in closedBall 0 (k + 1 : ℝ), ‖F (φ i) x - F (φ j) x‖) < ε := by
    apply integral_cauchy_of_approximations (fun j ↦ F (φ j))
      (fun n j ↦ mollify (F (φ j)) n) (fun n ↦ (1 / ((n : ℝ) + 1)) * C k)
      (fun j ↦ hFi j k)
      (fun n j ↦ (mollify_contDiff (hF (φ j)).continuous n).continuous.continuousOn
        |>.integrableOn_compact (isCompact_closedBall 0 _))
    · simpa only [zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (C k)
    · intro n j
      simp_rw [norm_sub_rev (F (φ j) _) (mollify (F (φ j)) n _)]
      apply integral_mollify_error_le_gradient_mass (hF (φ j)) n (hC k)
      simpa only [add_assoc, one_add_one_eq_two] using hbound (φ j) k
    · intro n
      obtain ⟨v, hv⟩ := hlim n k
      exact integral_cauchy_of_uniform_convergence (isCompact_closedBall 0 (k + 1 : ℝ))
        (fun j ↦ mollify (F (φ j)) n)
        (fun j ↦ (mollify_contDiff (hF (φ j)).continuous n).continuous.continuousOn
          |>.integrableOn_compact (isCompact_closedBall 0 _)) v hv
  have hlocal (k : ℕ) : ∃ V : Space d → ℝ, IntegrableOn V (closedBall 0 (k + 1 : ℝ)) ∧
      Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ), ‖F (φ j) x - V x‖) atTop (𝓝 0) :=
    exists_integral_limit_of_cauchy (volume.restrict (closedBall 0 (k + 1 : ℝ)))
      (fun j ↦ F (φ j)) (fun j ↦ hFi j k) (hc k)
  choose V hV hVlim using hlocal
  have hcompat (k l : ℕ) (hkl : k ≤ l) :
      V k =ᵐ[volume.restrict (closedBall 0 (k + 1 : ℝ))] V l := by
    have hs : closedBall (0 : Space d) (k + 1 : ℝ) ⊆ closedBall 0 (l + 1 : ℝ) :=
      closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hkl 1)
    exact ae_eq_of_integral_limits _ (fun j ↦ hFi j k) (hV k) ((hV l).mono_set hs)
      (hVlim k) (integral_limit_mono_set hs _ _ (fun j ↦ hFi j l) (hV l) (hVlim l))
  have hcover (x : Space d) : ∃ k : ℕ, x ∈ closedBall 0 (k + 1 : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    refine ⟨k, ?_⟩
    simp only [mem_closedBall, dist_zero_right]
    linarith
  obtain ⟨v, hv⟩ := exists_ae_gluing volume
    (fun k : ℕ ↦ closedBall (0 : Space d) (k + 1 : ℝ))
    (fun _ ↦ measurableSet_closedBall) hcover V hcompat
  have hvi (k : ℕ) : IntegrableOn v (closedBall 0 (k + 1 : ℝ)) :=
    (hV k).congr (hv k).symm
  have hvt (k : ℕ) : Tendsto
      (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ), ‖F (φ j) x - v x‖) atTop (𝓝 0) := by
    apply (hVlim k).congr'
    apply Eventually.of_forall
    intro j
    apply integral_congr_ae
    filter_upwards [hv k] with x hx
    rw [hx]
  refine ⟨φ, v, hφ, fun K hK ↦ ?_⟩
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Space d)
  obtain ⟨k, hk⟩ := exists_nat_gt r
  have hs : K ⊆ closedBall 0 (k + 1 : ℝ) :=
    hr.trans ((ball_subset_ball (by linarith)).trans ball_subset_closedBall)
  exact ⟨(hvi k).mono_set hs,
    integral_limit_mono_set hs _ _ (fun j ↦ hFi j k) (hvi k) (hvt k)⟩

/-- The original solution's translated primitives admit a common integral limit under
an all-center surface bound, uniformly over arbitrary choices of centers and positive scales. -/
theorem RigidityHypotheses.translated_primitive_global_integral_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) :
    ∃ (φ : ℕ → ℕ) (v : Space (m + 1) → ℝ), StrictMono φ ∧
      ∀ K : Set (Space (m + 1)), IsCompact K → IntegrableOn v K ∧
        Tendsto (fun j ↦ ∫ x in K,
          ‖phasePrimitive f (zeroExtension g u (c (φ j) + R (φ j) • x)) - v x‖)
            atTop (𝓝 0) := by
  apply exists_local_integral_subsequence_of_gradient_mass _
    (fun j ↦ locallyLipschitz_comp_translate_dilation
      (hr.phasePrimitive_zeroExtension_locallyLipschitz h) (c j) (R j))
    (fun j x ↦ h.phasePrimitive_mem_Icc
      ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
    (fun k ↦ L * (k + 2 : ℝ) ^ m)
  intro j k
  exact hr.translated_primitive_mass_le_surface_bound h hbound (c j) (hR j) (by positivity)

end SerrinEpigraph
