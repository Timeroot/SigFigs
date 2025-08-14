import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.RCLike.Basic

theorem Real.min_natPow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    min x y ^ n = min (x ^ n) (y ^ n) := by
  sorry

theorem Real.max_natPow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    max x y ^ n = max (x ^ n) (y ^ n) := by
  sorry

theorem Real.sqrt_mono : Monotone Real.sqrt :=
  fun _ _ ↦ Real.sqrt_le_sqrt
