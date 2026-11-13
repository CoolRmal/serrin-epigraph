module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

/-!
# Differentiable powers of the positive part

Powers at least two are continuously differentiable even where the positive part vanishes.
These are the test functions needed in the quotient-energy argument.
-/

public section

open Filter Set
open scoped Topology

namespace SerrinEpigraph

theorem hasDerivAt_positivePart_pow {k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ max t 0 ^ k) (k * max x 0 ^ (k - 1)) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : (fun t : ℝ ↦ max t 0 ^ k) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hx] with t ht
      simp [max_eq_right ht.le, show k ≠ 0 by omega]
    simpa [max_eq_right hx.le, show k - 1 ≠ 0 by omega] using
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  · have hp : HasDerivWithinAt (fun t : ℝ ↦ max t 0 ^ k) 0 (Ici 0) 0 := by
      have hd : HasDerivAt (fun t : ℝ ↦ t ^ k) 0 0 := by
        simpa [show k - 1 ≠ 0 by omega] using hasDerivAt_pow k (0 : ℝ)
      exact hd.hasDerivWithinAt.congr_of_mem (fun t ht ↦ by rw [max_eq_left ht])
        self_mem_Ici
    have hn : HasDerivWithinAt (fun t : ℝ ↦ max t 0 ^ k) 0 (Iic 0) 0 := by
      exact (hasDerivAt_const 0 (0 : ℝ)).hasDerivWithinAt.congr_of_mem
        (fun t ht ↦ by simp [max_eq_right ht, show k ≠ 0 by omega]) self_mem_Iic
    simpa [Ici_union_Iic, show k - 1 ≠ 0 by omega] using hp.union hn
  · have heq : (fun t : ℝ ↦ max t 0 ^ k) =ᶠ[𝓝 x] fun t ↦ t ^ k := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      rw [max_eq_left ht.le]
    simpa [max_eq_left hx.le] using (hasDerivAt_pow k x).congr_of_eventuallyEq heq

theorem contDiff_positivePart_pow {k : ℕ} (hk : 2 ≤ k) :
    ContDiff ℝ 1 (fun t : ℝ ↦ max t 0 ^ k) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun x ↦ (hasDerivAt_positivePart_pow hk x).differentiableAt
  · have heq : deriv (fun t : ℝ ↦ max t 0 ^ k) = fun x : ℝ ↦ k * max x 0 ^ (k - 1) :=
      funext fun x ↦ (hasDerivAt_positivePart_pow hk x).deriv
    rw [heq]
    exact continuous_const.mul ((continuous_id.max continuous_const).pow _)

end SerrinEpigraph
