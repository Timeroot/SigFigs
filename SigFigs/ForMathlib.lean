import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.RCLike.Basic

theorem Real.min_natPow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    min x y ^ n = min (x ^ n) (y ^ n) := by
  rcases min_cases x y with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [h₁, left_eq_inf]
    exact pow_le_pow_left₀ hx h₂ n
  · rw [h₁, right_eq_inf]
    exact pow_le_pow_left₀ hy h₂.le n

theorem Real.max_natPow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    max x y ^ n = max (x ^ n) (y ^ n) := by
  rcases max_cases x y with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [h₁, left_eq_sup]
    exact pow_le_pow_left₀ hy h₂ n
  · rw [h₁, right_eq_sup]
    exact pow_le_pow_left₀ hx h₂.le n

@[mono]
theorem Real.sqrt_monotone : Monotone Real.sqrt :=
  fun _ _ ↦ Real.sqrt_le_sqrt

--PR'ed, see #28416
instance
    {α : Type u_1} {β : Type u_2} [Preorder α] [Preorder β]
    [TopologicalSpace α] [TopologicalSpace β] [OrderTopology α] [OrderTopology β]
    : ContinuousMapClass (α ≃o β) α β where
  map_continuous := OrderIso.continuous
