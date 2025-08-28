import SigFigs.FOBall

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Examples of First-Order Ball Arithmetic

It's recommended that you look at `IntervalExamples` first to get a general idea of the
conventions. Unlike interval arithmetic, first-order ball arithmetic adds errors in quadrature
(treating them as "independent errors" in some pseudo-Gaussian sense), propgates values through
functions by evaluating at the midpoint, and scaling derivatives to scale uncertainties.

This is, often, what scientists mean by "uncertainty propagation".
-/

/-! # Example physics problem

Example problem: you drop a ball from a height of 150.0m.
After 5.18 seconds, how far is it above the ground?
Answer: Use the formula `h = h₀ - 1/2 g t²`. This evaluates to 19 seconds.
-/

example
    (g t height : FOBall)
    (hg : g = 9.8) --Interpreted as number 9.8 with a standard deviation of 0.05
    (ht : t = 5.18) --Interpreted as number 5.18 with a standard deviation of 0.005
    (h_height : height = 150.0) --Interpreted as number 150.0 with a standard deviation of 0.05

  --If you plug those three numbers in to `h₀ - 1/2 g t` and propagate uncertainties with full
  -- precision, you get the mipoint 18.52124. The FOBall type stores the _variance_ (so, the)
  -- square of the uncertainty) to avoid irrational numbers where possible, and the variance
  -- works out to be 0.4846983523. Side note: the variance is an NNReal.
  --So, this is an exact equality:
  : height - (1 / 2) * g * t^2 = ⟨18.52124, 0.4846983523⟩ := by
  subst g t height
  ext <;> norm_num [pow_two]

/-
You can compare these numbers with the corresponding examples in `IntervalExamples.lean`.
There, the exact answer was `18.5198225 ± 0.974630625`. For one, the midpoint values don't
agree, because the `t^2` is a nonlinear function and doesn't preserve midpoints. Second,
the effective uncertainty is larger in the interval arithmetic setting compared to the
the first-order ball setting. (The uncertainty here is √0.4847 ≈ 0.6962)
-/

/-
But requiring an answer to full precision is unreasonable (and, if there are irrational numbers
involved, impossible to give as a decimal). A more reasonable form would be saying that 19
is consistent with the values given:
-/
example (g t height : FOBall) (hg : g = 9.8) (ht : t = 5.18) (h_height : height = 150.0)
  : 19 ∈ height - (1/2) * g * t^2 := by
  subst g t height
  norm_num [FOBall.mem_def, pow_two]

/-
Like with interval arithmetic, multiple answers could be _consistent_.

In the example above, `18.1` and `18.6892384901` are also consistent
consistent, but have way too many digits of precision for their accuracy.
Both of these would be typically marked wrong in a classroom setting,
and this would be a bad formalization.
-/
example (g t height : FOBall) (hg : g = 9.8) (ht : t = 5.18) (h_height : height = 150.0)
  : (18.1 ∈ height - (1/2) * g * t^2) ∧ (18.6892384901 ∈ height - (1/2) * g * t^2) := by
  subst g t height
  norm_num [FOBall.mem_def, pow_two]

/-- This version says 19 is consistent, and the variance is in the first digit after
the decimal point. A TODO item is writing a better notation for this, like `≈` for
interval arithmetic.
-/
example (g t height : FOBall) (hg : g = 9.8) (ht : t = 5.18) (h_height : height = 150.0)
  (ans : FOBall) (h_ans : ans = height - (1/2) * g * t^2)
  : 19 ∈ ans ∧ 0.1 ≤ √ans.var ∧ √ans.var ≤ 1 := by
  sorry

/-! # Example Calculus Problem

Problem: Compute the integral of `(1 + x) / (1 + x^2)` from 0 to 1. Answer to 3 decimal
places.

Answer: 1.132.
-/

/- This was an example from IntervalExamples.lean, but it would be quite strange to use
this version with FOBall! FOBall is a datatype for uncertainty _propagation_, from initially
unclear measurements. There is no uncertain inputs here. You can write something like the
below, and it's logically equivalent to the interval version, but this is certainly
an **incorrect** formalization. -/
example : ∫ x in 0..1, (1 + x) / (1 + x^2) ∈ (1.132 : FOBall) := by
  sorry


/-! # Mapping functions

Nonlinear functions propagate FOBall's by mapping the midpoint estimate, and scaling
the standard deviation by the derivative. Like ℝRange, the mapped version is available
as a FunLike coercion, but this instance is scoped behind the FOBall namespace.

Without that namespace open, it doesn't coerce:
-/

/--
error: Type mismatch
  Real.sqrt
has type
  ℝ → ℝ
but is expected to have type
  FOBall → FOBall
-/
#guard_msgs in
example : (Real.sqrt : FOBall → FOBall) 3.5 = 1776 := by
  sorry

/- But like this, it works. -/
open scoped FOBall in
example : (Real.sqrt : FOBall → FOBall) 3.5 = 1776 := by
  sorry

/- You can also trigger this through the FunLike coercion notation `⇑`, or explicitly
by invoking `FOBall.map`. -/
open scoped FOBall in
example : ⇑Real.sqrt 3.5 = 1776 := by
  sorry

example : FOBall.map Real.sqrt 3.5 = 1776 := by
  sorry

/- If you don't use `⇑` or explicitly mention FOBall, then it will use the standard Real
version. This example is an equality of reals, oops! -/
open scoped FOBall in
example : Real.sqrt 3.5 = 1776 := by
  sorry

/- Here's an actual true example: `log (1±0.5) = 0±0.5`. -/
open scoped FOBall in
example : ⇑Real.log 1e0 = ⟨0, 1/4⟩ := by
  ext
  · simp
  · simp
    rw [FOBall.map_differentiableAt _ _ (by simp)]
    norm_num
