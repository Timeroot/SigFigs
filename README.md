# Uncertainty Propgation for Lean

**SigFigs** is a package practical and pedagogical [uncertainty propagation](https://en.wikipedia.org/wiki/Propagation_of_uncertainty) in [Lean 4](https://lean-lang.org/). Given some input data, with some beliefs about its possible or plausible values, how do we establish the values after some transformations on the data?

Lean's is a formal theorem prover, and its mathematics library [Mathlib](https://github.com/leanprover-community/mathlib4) is geared towards precise mathematics. Uncertainty propagation takes place within a model of uncertainty, which is a set of assumptions and approximations about the data and the transformations. For instance, in the case of a linear combination of uncertain variables, we might assume that the input variables are independent - or not. When applying a nonlinear transformation, we might standarize (especially within, say, a classroom environment) that we propagate through using the [delta method](https://en.wikipedia.org/wiki/Delta_method) or a first-order Taylor expansion. The package provides a framework for defining such models, and then propagating uncertainty through them with provable conclusions _within the given model_.

## Models

The package provides three models of uncertainty:
- **Interval**: The input data is given as an interval, and the output is also an interval. All operations (addition, multiplication, nonlinear functions...) contain the entire image of the input interval. This is the most strict and mathematically precise model, and is amenable to use in downstream theorem proving, as it can prove rigorous bounds on the output. On the other hand, it is often difficult to adapt to real-world scenarios, where the worst-case bounds can be unrealistically large. This is given as the `ℝRange` type.
- **First-order Ball Arithmetic**: The input data is given as a center and a radius, which is most accurately interpreted as a [sensitivity](https://en.wikipedia.org/wiki/Sensitivity_analysis) but can also be interpreted as a standard deviation or [https://flintlib.org/doc/using.html](ball) width. Sensitivity propagates through differentiable[^1] functions through scaling. The center maps directly through functions, meaning that it does not necessarily track the mean through nonlinear transformations, but can be interpreted as a median when transformations are monotonic. This is given as the `FOBall` type.
- **Significant Figures**: The input data is given as a center and a number of significant figures, which is the simplest and most intuitive way to express uncertainty in many real-world scenarios. This is typically what is used in some grade-school or early undergraduate science classes. It is produces highly readable intermediate states, as the output is always cleanly representable as a decimal string of finite length. On the other hand, it enjoys the _least_ abstract mathematical properties, in which addition and multiplication are non-associative and essentially all bounds are heuristic. But, it remains of great pedagogical importance. This is given as the `SigFigs` type.

## Usage

The first and foremost goal of this package is to allow textbook-style problems with uncertainty to be stated naturally in Lean in a way that captures the semantics intended by the problem. For instance, consider the problem:
```lean4
/-
Example problem: you drop a ball from a height of 150.0m.
After 5.18 seconds, how far is it above the ground?

Answer: Use the formula `h = h₀ - 1/2 g t²`. This evaluates to 19 seconds.
-/
example (g t height : ℝRange) (hg : g = 9.8) (ht : t = 5.18) (h_height : height = 150.0)
  : height - (1/2) * g * t^2 ≈ 19. := by
  sorry
```
This problem implicitly has uncertainty quantities in the inputs, and earth's gravity `9.8` is intrinsically imprecise as it varies across the globe. The `≈` operator is used to indicate that the output is an approximation to the correct accuracy, and the `ℝRange` type is used to represent the input data. Arithmetic operations such as `*` and `^` are overloaded to work with the `ℝRange` type to propagate uncertainty through. The numeric literals `9.8` are interpreted as `ℝRange` values with the correct accuracy.

As another example, consider the problem of adding two uncertain values:
```
/- Alice has a box of chocolates that weighs 100g ± 3g, and Bob has a box of chocolates that weighs 30g ± 15g. How much do they have together? -/
example (A B : ℝRange) (hA : A = 100 ± 3) (hB : B = 30 ± 15) :
    A + B = 130 ± 18 := by
  sorry
```

The third goal is to make the package reasonably useful for actually carrying out these calculations. When only field operations are used, all numbers remain rational and Lean's `norm_num` tactic can be used to evaluate the expressions. A significant next goal would be integrating [ComputableReal](https://github.com/Timeroot/ComputableReal) and/or Geoffrey Irving's [interval](https://github.com/girving/interval/) packages to allow for mostly automatic evaluation of expressions involving square roots, exponentation, or trigonometric functions.

The most complete tutorial is in the example files, one for [ℝRange](SigFigs/Examples/IntervalExamples.lean), one for [FOBall](SigFigs/Examples/FOBallExamples.lean). It remains to write one for the Significant Figures model.

## Contributing

We welcome contributions. Currently the goals would be, in order of priority:
1. Ensure thorough support for all field operations on all three models of uncertainty. This should include proofs, where possible, that membership is an invariant under the operations on intervals.
2. Operations and theorems for interconverting between the three models of uncertainty. For instance, converting an `ℝRange` to a `FOBall` or `SigFigs`, and vice versa. Theorems about when these conversions are valid, and when they are not. For instance, converting an `ℝRange` to a `FOBall` commutes with addition, but not multiplication.
3. Add simplification lemmas were possible for nonlinear transformations. For instance, `Real.exp` is monotone and so the output of `Real.exp` on an `ℝRange` simply maps the endpoints; this should be a simp lemma.
5. Add appropriate calculation lemmas for these nonlinear transformations, so that they be discharged readily (either by `norm_num`, `native_decide`, `interval`, or perhaps some custom combination).

[^1]: The package can currently generalize slightly beyond differentiable functions, to any function that is _locally Lipschitz continuous_. This becomes especially important when propagating through e.g. the absolute value function, which is not differentiable at zero.