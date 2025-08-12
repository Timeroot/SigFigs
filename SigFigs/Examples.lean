import SigFigs.Interval

--For the examples with complicated functions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

--Parsing examples
#check (1.23 : ℝRange)
#check (1.23ₑₓ : ℝRange)
#check (1.23 + (Real.sqrt 7 : ℝ) : ℝRange)
#check (3e10 : ℝ) + (5e10 : ℝRange)
#check 1.23ᵤ -- u subscript for "uncertain"; `fooᵤ` elaborates the same as `(foo : ℝRange)`.

#check 7 ± 1
--Elaborates as x±2, even though we construct the interval "manually".
open Real in
#check let x : ℝ := π; (⟨⟨x-2, x+2⟩, by linarith⟩ : ℝRange)
--Does not use ± notation because it's not a manifestly symmetric expression
#check let x : ℝ := 37; (⟨⟨x-2, x+5⟩, by linarith⟩ : ℝRange)

example : 1.23ₑₓ = (123 / 100 : ℝ) := by
  ext <;> norm_num

/- The number `1500km`, in a scientific setting, would often be understood to be
only precise to the first nonzero digit. This can be expressed as `1.5e3` here.
-/
example : 1.5e3 = 1500±50 := by
  ext <;> norm_num

/-
Note that some authors would use `1500km` to mean four digits of precision, which
we would write `1.500e3` or `1500e0`, and would use `1.5e3` to mean two digits of precision.
-/
example :
    1.500e3 = (1500e0 : ℝRange) ∧
    1.500e3 ≠ (1.5e3  : ℝRange) := by
  constructor
  · ext <;> norm_num
  · norm_num [ne_eq, NonemptyInterval.ext_iff, Prod.ext_iff]

example :
    137e0 = 1.37e2ᵤ ∧ --The ...ᵤ notation is short (... : ℝRange) here
    137.  = 1.37e2ᵤ ∧
    137   ≠ 1.37e2ᵤ := by
  and_intros
  · ext <;> norm_num
  · ext <;> norm_num
  · norm_num [ne_eq, NonemptyInterval.ext_iff, Prod.ext_iff]

/-! # Example physics problem

Example problem: you drop a ball from a height of 150.0m.
After 5.18 seconds, how far is it above the ground?
Answer: Use the formula `h = h₀ - 1/2 g t²`. This evaluates to 19 seconds.
-/

example
    (g t height : ℝRange)
    (hg : g = 9.8) --Interpreted as the interval [9.75, 9.85]
    (ht : t = 5.18) --Interpreted as the interval [5.175, 5.185]
    (h_height : height = 150.0) --Interpreted as the interval [149.5, 150.5]
  : height - 0.5 * g * t^2 = 19 := by
  --This would be an INCORRECT formalization, for two reasons:
  -- * The literal `0.5` would be interpreted as the interval `[0.45, 0.55]`,
  --    which isn't the intended meaning here. It's an exact mathematical constant.
  -- * The answer is not exactly equal to the number 19. (So, as written, this is unprovable.)
  --   That would mean the only answer consistent with the input data is precisely 19.
  sorry

/-
This would be at least a correct formalization, as we now give the exact
error bounds on the RHS, and so this would be an equality of intervals. But,
obviously, this a much stricter acceptance criterion for an answer than would
be typical in a physics classroom environment.

But, it could be a reasonable model for what happens in a scientific research
setting, where uncertainties are tracked with high precision.
-/
example (g t height : ℝRange) (hg : g = 9.8) (ht : t = 5.18) (h_height : height = 150.0)
  : height - (1/2) * g * t^2 = 18.5198225±0.974630625 := by
  sorry

/-
This is equivalent to the above. Here, we use the `0.5ₑₓ` notation to mean
that the number `0.5` is an exact constant, with zero uncertainty. And instead
of giving the interval as `x ± y`, we give the interval explicitly. But this
is, like above, too strict for a classroom setting.
-/
example (g t height : ℝRange) (hg : g = 9.8) (ht : t = 5.18) (h_height : height = 150.0)
  : height - 0.5ₑₓ * g * t^2 = ⟨(17.545191875, 19.494453125), by linarith⟩ := by
  sorry

/-
This version of the statement says that `19` is an answer _consistent_ with the output
interval. This captures more typically the intent of the question. This captures what
a scientist might mean by "we can't rule out the null hypothesis that it's equal to 19".
-/
example (g t height : ℝRange) (hg : g = 9.8) (ht : t = 5.18) (h_height : height = 150.0)
  : 19 ∈ height - (1/2) * g * t^2 := by
  sorry

/-
Note that multiple answers could be _consistent_. It turns out that 18 is also consistent
with the interval; the below is just as true as the above. `18.6892384901` is also
consistent, but has way too many digits of precision. Both of these would be typically
marked wrong in a classroom setting.
-/
example (g t height : ℝRange) (hg : g = 9.8) (ht : t = 5.18) (h_height : height = 150.0)
  : (18 ∈ height - (1/2) * g * t^2) ∧ (18.6892384901 ∈ height - (1/2) * g * t^2) := by
  sorry

/-- This version says that the answer is consistent with `19`, and that the uncertainty
in the number `19` is correct to the nearest number of significant figures.
-/
example (g t height : ℝRange) (hg : g = 9.8) (ht : t = 5.18) (h_height : height = 150.0)
  : height - (1/2) * g * t^2 ≈ 1.9e1 := by
  sorry

/-! # Example Calculus Problem

Problem: Compute the integral of `(1 + x) / (1 + x^2)` from 0 to 1. Answer to 3 decimal
places.

Answer: 1.132.
-/

/- Here the left hand side is exact, and we're given a precision to use. So, we use
that value on the right hand side. The `ᵤ` (for "uncertainty") tells Lean that the right
hand side should be interpreted as an interval, and it correctly infers the accuracy
based on the digits of precision given. We use `∈` since we're checking for membership
of an exact real number in an interval. -/
example : ∫ x in 0..1, (1 + x) / (1 + x^2) ∈ 1.132ᵤ := by
  sorry

/-! # Example Black-Scholes Calculation

Problem:

Calculate the price of a European call option with the following characteristics:
  * Current Stock Price (S): $100
  * Strike Price (K): $100
  * Time to Expiration (T): 1 year
  * Risk-Free Interest Rate (r): 5%
  * Volatility (σ): 20%

Answer: The price of the call option approximately $10.45.
-/

/- In this economic context, there is typically an implicit desire to give accuracies of
one cent, so, two decimal points. Typically one would treat all inputs to be exact. -/

--Define the Black—Scholes model, which uses 𝒩(x), the CDF of the normal distribution.
noncomputable def NormalCDF : ℝ → ℝ :=
  ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)

/-- Price of an option by the European Black—Scholes model, where:
 * S₀​ is the current stock price.
 * K is the strike price.
 * T is the time to expiration in years.
 * r is the risk-free interest rate.
 * σ is the volatility of the stock's returns.
-/
noncomputable def EuropeanBlackScholesModel (S₀ K r T σ : ℝ) : ℝ :=
  let d₁ : ℝ := (Real.log (S₀ / K) + (r + σ^2 / 2) * T) / (σ * √T);
  let d₂ : ℝ := d₁ - σ * √T;
  S₀ * NormalCDF d₁ - K * Real.exp (-r * T) * NormalCDF d₂

/- The answer is $10.45, to the nearest cent. -/
example : EuropeanBlackScholesModel 100 100 1 0.05 0.20 ∈ 10.45ᵤ := by
  sorry

/-! # Example Geometry Problem

Problem: I measure the area of a circle to be 5.9m². What's the radius?

Answer: idk
-/

open Real in
/- This combines measurement uncertainty with an exact number, π. -/
example (A r : ℝRange) (hA : A = 5.9) (h_area : A = π * r^2) :
    r ≈ 1.37 := by
  sorry


/- # Example Geometry Problem with excess precision

Problem: I measured the area of a rectangle in square inches and got 3.1in².
Then I measured its perimeter in meters, because I _hate_ consistent
unit systems - and I got the same number, 3.1. Wow, what're the chances.
What's the diagonal of the rectangle, in millimeters?

Answer: 1549mm.
-/

/- "Answer to the nearest millimeter" means that, with the answer in that unit,
we want something accurate to the ones place. Remember that the conversion between
inches and meters is *exactly* 0.0254 inches per meter.

If this was just a problem about exact real numbers, this would make most sense to
parameterize by the width and height of the rectangle. But we didn't measure those
directly. So, we say that we know constraints on their values, lying in the measurements
given, and then check that the output is consistent. That would be the most
rigorous version ... but doesn't really reflect the spirit of the problem, at this level.

In this problem, as it turns out, the numbers 1523mm through 1573mm are all
consistent with the uncertainty; the "midpoint" value is 1548.7mm. In that sense,
the problem asked for too much precision. So it's best to fall back to interpreting
the input numbers as exact. This is reasonable, given that this likely comes from
a math class, where uncertainty and significant figures are typically ignored.
-/
example
  (w_in h_in w_mm h_mm : ℝ)  -- The exact, true values
  (h_convert_w : w_mm = 25.4 * w_in) -- Exact conversion
  (h_convert_h : h_mm = 25.4 * h_in) -- Exact conversion
  (h_area : w_in * h_in = 3.1) --Our first measurement, in in². We treat this as exact,
                               -- for this math problem.
                               -- We would write `∈ 3.1ᵤ` in a physics problem setting.
  (h_perim : 2 * 1000 * (w_mm + h_mm) = 3.1) --Our second measurement, in meters
  : √(w_mm^2 + h_mm^2) ∈ 1.549e3ᵤ := by --The answer is rounded off after three digits.
  sorry

/-! # Example of plus/minus notation

Box A has 100±3 balls, and Box B has 30±15 balls. What range of balls would there be
when they're combined?

Answer: 130±18.
-/

/- Here we use exact equality of intervals, since we know that it's all integers and
this will be exact.

Note that in _some_ contexts, such as undergraduate physics labs, ± errors are expected
to add like independent standard deviations, so that `a ± x` and `b ± y` add to
`(a + b) ± √(x^2 + y^2)`. This is not the error model for ℝRange (interval arithmetic)
and will be developed separately.
-/
example (A B : ℝRange) (hA : A = 100 ± 3) (hB : B = 30 ± 15) :
    A + B = 130 ± 18 := by
  sorry
