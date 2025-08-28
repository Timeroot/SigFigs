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

section parsing

/- Like ℝRange, we can infer this from decimals or from a `±` notation. We need to
`open scoped FOBall` to get the latter notation accessible. -/
open scoped FOBall

#check 1 ± 157 --A very vague number, indicating a "measurement" of 1 with an uncertainty of
               --157 in that reading.

#check (1.5 : FOBall) --Equivalent to `1.5 ± 0.05`
#check (15e-1 : FOBall) --The same as the above
#check (1.50 : FOBall) --This is higher precision, meaning `1.5 ± 0.005`.
#check (150e3 : FOBall) --Equivalent to `150000 ± 500`.
#check (15 : FOBall) --Equivalent to `15 ± 0`. This is a precise quantity!
#check (Real.pi : FOBall) -- Similarly, any real can be cast to a precise quantity.

--Without anything noted as an FOBall, the `3.5` parses as a Float or Real. The resulting
--quantity is not an approximate quantity.
#check 3.5 + Real.pi

--Now the right term is an FOBall (because of the ± notation),
--so 3.5 on the left parses as an FOBall too.
#check 3.5 + (5 ± 1)

--Here `x` is the precise number `Pi`, but then cast to an FOBall. This causes the
--number 6.7 to also parse as an FOBall. The parenthesized quantity is then equal to
--`(67/100 + 7π) ± 0.05`. We can apply the lifted version of `Real.sin` to this
--uncertain expression to get some nonlinear estimate with uncertainty (more on function
--application below).
#check (letI x : FOBall := Real.pi; ⇑Real.sin (7 * x + 6.7))

end parsing

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

open scoped FOBall in --for the ± notation
/-- This version says 19 is consistent, and that the given uncertainty (of ±1) is "roughly"
right - within a factor of 4. See `FOBall.isApprox`, and the corresponding interval example,
for some more on this form.

The right-hand side could also have been written as  `⟨19, 1⟩` (which would be equal to
`19±1`).

Other correct answers would be `1.9e1`, `19e0`, `⟨19, 0.25⟩`. These are
all equal and have uncertainties of ±0.5.

Writing `19` on the RHS would be wrong (since it has zero uncertainty and so would imply
exact equality). Writing `19.0` would imply an uncertainty of `0.05` instead of `0.5`, and
also be wrong.
-/
example (g t height : FOBall) (hg : g = 9.8) (ht : t = 5.18) (h_height : height = 150.0)
  (ans : FOBall) (h_ans : ans = height - (1/2) * g * t^2)
  : ans ≈ 19±1 := by
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

/- Here's an actual true example: `log (1±0.5) = 0±0.5`. The uncertainty stays the same
because the derivative of `Real.log` at 1 is itself 1, so there's no scaling involed. -/
open scoped FOBall in
example : ⇑Real.log 1e0 = ⟨0, 1/4⟩ := by
  ext
  · simp
  · simp
    rw [FOBall.map_differentiableAt _ _ (by simp)]
    norm_num
