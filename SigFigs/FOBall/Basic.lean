import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

import SigFigs.ForMathlib

open NNReal

/-! # First-Order Ball Arithmetic

A **first-order ball** models a real number with uncertainty using a center value and a width
(which can be thought of a variance of a random variable), with semantics to propagate them
through arithmetic operations by acting on the center(s) to produce a new center, and scaling
the width based on the derivative for nonlinear functions. In this sense, it can be viewed
as arithmetic on the tangent space of the real line.

Three key points to be aware of here:
 * If we interpret a value `x±σ` as representing a normally distributed variable `𝒩(x, σ)`,
   and pass it through a nonlinear function, the output does not necessarily reflect the
   mean or variance of the output distribution. Rather, the new "midpoint" is f(x).
 * For two-argument functions, this treats intputs as independent variables. This means
   that `(x±a) + (y±b) = (x+y) ± √(a^2 + b^2)`, for instance. In particular,
   `2 * (x±a) = 2x ± 2a` is not equal to `(x±a) + (x±a) = 2x ± (√2 * a)`. Similarly,
   `x^2 ≠ x*x`.
 * This model is slightly more flexible than just the tangent space calculation: we don't
   need the maps to be differentiable to have a well-defined image, we can make do with
   any local lipschitz constant `k`, which will scale the variance by `k^2`.

We store these as a midpoint and variance (as opposed to standard deviation), since this means
that arithmetic can be done without involving square roots.

This is a version of the [delta method](https://en.wikipedia.org/wiki/Delta_method) for
uncertainty propagation.

## References

 * "An Introduction to Error Analysis: The Study of Uncertainties in Physical Measurements" by
   John Richard Taylor. [Google Books](https://books.google.ca/books/about/An_Introduction_to_Error_Analysis.html?id=U0YoQQAACAAJ&source=kp_book_description&redir_esc=y)
-/

@[ext]
structure FOBall where
  mid : ℝ
  var : ℝ≥0

namespace FOBall

instance : Zero FOBall :=
  ⟨⟨0, 0⟩⟩

instance : One FOBall :=
  ⟨⟨1, 0⟩⟩

instance : NatCast FOBall :=
  ⟨fun n ↦ ⟨n, 0⟩⟩

instance : IntCast FOBall :=
  ⟨fun z ↦ ⟨z, 0⟩⟩

instance : RatCast FOBall :=
  ⟨fun q ↦ ⟨q, 0⟩⟩

/-- Addition of `FOBall`s adds "in quadrature", so variances add linearly. -/
instance : Add FOBall :=
  ⟨fun x y ↦ ⟨x.mid + y.mid, x.var + y.var⟩⟩

instance : Neg FOBall :=
  ⟨fun x ↦ ⟨-x.mid, x.var⟩⟩

instance : Sub FOBall :=
  ⟨fun x y ↦ x + -y⟩

/-- For multiplication we define (conforming to the "first-order" philosophy) a new variance of
`(x * y).var = x.var * y.mid^2 + y.var * x.mid^2`, in other words that
`V[XY] = V[X] 𝔼[Y]^2 + V[Y] 𝔼[X]^2`. This is the convention in _Taylor, Error Analysis_.

There is at least one other reasonable quantity one might expect, which is
`V[XY] = V[X] 𝔼[Y]^2 + V[Y] 𝔼[X]^2 + V[X] V[Y]`, which is the correct variance for
a product of normally distributed variables.
-/
instance : Mul FOBall :=
  ⟨fun x y ↦ ⟨x.mid * y.mid, x.var * ‖y.mid‖₊^2 + y.var * ‖x.mid‖₊^2⟩⟩

/-!
An aside: this definition of addition and multiplication leads to a non-distributive algebraic
structure. The midpoints agree - they just undergo standard real arithmetic! - but the variances
differ. To understand why, let's consider `(X * (Y + Z)).var` and `(X * Y + X * Z).var`.
```
V[X(Y+Z)] = (true when X vs. Y+Z independent, to first order in V's)
V[X] 𝔼[Y+Z]^2 + V[Y+Z] 𝔼[X]^2 = (linearity of 𝔼)
V[X] (𝔼[Y] + 𝔼[Z])^2 + V[Y+Z] 𝔼[X]^2 = (true when Y vs. Z independent)
V[X] (𝔼[Y] + 𝔼[Z])^2 + (V[Y] + V[Z]) 𝔼[X]^2 = (algebra)
V[X] 𝔼[Y]^2 + 2 V[X] 𝔼[Y] 𝔼[Z] + V[X] 𝔼[Z]^2 + V[Y] 𝔼[X]^2 + V[Z] 𝔼[X]^2
≠
V[X] 𝔼[Y]^2 +                    V[X] 𝔼[Z]^2 + V[Y] 𝔼[X]^2 + V[Y] 𝔼[Z]^2 = (algebra)
(V[X] 𝔼[Y]^2 + V[Y] 𝔼[X]^2) + (V[X] 𝔼[Z]^2 + V[Y] 𝔼[Z]^2) = (true when X vs. Z independent, to first order in V's)
(V[X] 𝔼[Y]^2 + V[Y] 𝔼[X]^2) + V[XZ] = (true when X vs. Y independent, to first order in V's)
V[XY] + V[XZ] = (true when XY vs. XZ independent)
V[XY + XZ]
```
By treating the errors in `XY` and `XZ` as independent, instead of appropriately correlated,
we underestimate the variance.
-/

noncomputable instance : Inv FOBall :=
  ⟨fun x ↦ ⟨x.mid⁻¹, x.var / ‖x.mid‖₊^2⟩⟩

noncomputable instance : Div FOBall :=
  ⟨fun x y ↦ x * y⁻¹⟩

instance instPowNat : Pow FOBall ℕ where
  pow x n := ⟨x.mid ^ n, if n = 0 then 0 else x.var * ‖x.mid‖₊ ^ (2 * (n - 1))⟩

instance instSMul : SMul ℕ FOBall where
  smul n x := ⟨n • x.mid, n^2 • x.var⟩

theorem zero_def : (0 : FOBall) = ⟨0, 0⟩ :=
  rfl

theorem natCast_def (n : ℕ) : (n : FOBall) = ⟨n, 0⟩ :=
  rfl

theorem intCast_def (z : ℤ) : (z : FOBall) = ⟨z, 0⟩ :=
  rfl

theorem ratCast_def (q : ℚ) : (q : FOBall) = ⟨q, 0⟩ :=
  rfl

theorem one_def : (0 : FOBall) = ⟨0, 0⟩ :=
  rfl

theorem add_def (x y : FOBall) : x + y = ⟨x.mid + y.mid, x.var + y.var⟩ :=
  rfl

theorem neg_def (x : FOBall) : -x = ⟨-x.mid, x.var⟩ :=
  rfl

theorem sub_def (x y : FOBall) : x - y = ⟨x.mid - y.mid, x.var + y.var⟩ :=
  rfl

theorem mul_def (x y : FOBall) : x * y =
    ⟨x.mid * y.mid, x.var * ‖y.mid‖₊^2 + y.var * ‖x.mid‖₊^2⟩ :=
  rfl

theorem inv_def (x : FOBall) : x⁻¹ = ⟨x.mid⁻¹, x.var / ‖x.mid‖₊^2⟩ :=
  rfl

theorem div_def (x y : FOBall) : x / y = ⟨x.mid / y.mid,
    x.var / ‖y.mid‖₊^2 + (y.var / ‖y.mid‖₊^2) * ‖x.mid‖₊^2⟩ := by
  suffices x.var / ‖y.mid‖₊^2 = x.var * ‖y.mid⁻¹‖₊^2 by
    rw [this]; rfl
  field_simp

@[simp]
theorem mid_zero : mid 0 = 0 := by
  rfl

@[simp]
theorem var_zero : var 0 = 0 := by
  rfl

@[simp]
theorem mid_one : mid 1 = 1 := by
  rfl

@[simp]
theorem var_one : var 1 = 0 := by
  rfl

@[simp]
theorem mid_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : FOBall).mid = n := by
  rfl

@[simp]
theorem var_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : FOBall).var = 0 := by
  rfl

--TODO: simps for IntCast / RatCast

@[simp]
theorem mid_add (x y : FOBall) : (x + y).mid = x.mid + y.mid := by
  rfl

@[simp]
theorem var_add (x y : FOBall) : (x + y).var = x.var + y.var := by
  rfl

@[simp]
theorem mid_neg (x : FOBall) : (-x).mid = -x.mid := by
  rfl

@[simp]
theorem var_neg (x : FOBall) : (-x).var = x.var := by
  rfl

@[simp]
theorem mid_sub (x y : FOBall) : (x - y).mid = x.mid - y.mid := by
  rfl

@[simp]
theorem var_sub (x y : FOBall) : (x - y).var = x.var + y.var := by
  rfl

@[simp]
theorem mid_mul (x y : FOBall) : (x * y).mid = x.mid * y.mid := by
  rfl

@[simp]
theorem var_mul (x y : FOBall) : (x * y).var =
    x.var * ‖y.mid‖₊^2 + y.var * ‖x.mid‖₊^2 := by
  rfl

theorem var_mul_toReal (x y : FOBall) : ((x * y).var : ℝ) =
    x.var * y.mid^2 + y.var * x.mid^2 := by
  simp

@[simp]
theorem mid_inv (x : FOBall) : (x⁻¹).mid = x.mid⁻¹ := by
  rfl

@[simp]
theorem var_inv (x : FOBall) : (x⁻¹).var = x.var / ‖x.mid‖₊^2 := by
  rfl

theorem var_inv_toReal (x : FOBall) : ((x⁻¹).var : ℝ) = x.var / x.mid^2 := by
  simp

@[simp]
theorem mid_div (x y : FOBall) : (x / y).mid = x.mid / y.mid := by
  rfl

@[simp]
theorem var_div (x y : FOBall) : (x / y).var =
    x.var / ‖y.mid‖₊^2 + y.var * ‖x.mid / y.mid‖₊^2 := by
  field_simp [div_def]

theorem var_div_toReal (x y : FOBall) :  ((x / y).var : ℝ) =
    x.var / y.mid^2 + y.var * (x.mid / y.mid)^2 := by
  field_simp

/-!
We're so close to having a proper CommSemiring, but alas we miss distributivity.
We're not an additive group, because `a + (-a) ≠ 0` whenever `a.var ≠ 0`.
We're not a GroupWithZero, because `a * a⁻¹ ≠ 1` whenever `a.var ≠ 0`.
We're not a MulDivCancelClass, because `1 * (0±1) / (0±1)⁻¹ = 0 ≠ 1`.
We're not an InvolutiveInv, because `(0±1)⁻¹⁻¹ = (0±0)⁻¹ = 0 ≠ 0±1.
We're not a CancelCommMonoid, because `(0±1) * ·` is not injective.
We're not a NoZeroDivisors, because `(0±1) * (0±1) = 0`, but if we included the "second order"
 term in multiplication, we would be.
-/

instance : AddCancelCommMonoid FOBall where
  add_assoc := by intros; simp [add_def, add_assoc]
  zero_add := by simp [FOBall.ext_iff]
  add_zero := by simp [FOBall.ext_iff]
  add_comm := by intros; simp [add_def, add_comm]
  add_left_cancel := by
    intro _ _ _ h
    simpa [FOBall.ext_iff] using h
  /- TODO: How do we hide this instance? We have it "by default" as soon as we have
    a AddMonoid (and we do), but it's not the semantics that we want. We want our
    instSMul to be higher priority when writing something down. We'll still have
    moderately crappy cases where (due to some rewrites) we end up with a `2 • ·`
    expression using the wrong instance, but that might just be what we have to live
    with.
  -/
  nsmul := nsmulRec

instance : AddCommMonoidWithOne FOBall where
  natCast_zero := by simp [zero_def, natCast_def]
  natCast_succ := by simp [add_def, natCast_def]

instance : SubtractionCommMonoid FOBall where
  neg_neg _ := by simp [FOBall.ext_iff]
  neg_add_rev _ _ := by simp [FOBall.ext_iff, add_comm]
  neg_eq_of_add := by
    rintro ⟨m₁, v₁⟩ ⟨m₂, v₂⟩ h
    simp [FOBall.ext_iff] at h
    rcases h with ⟨h, rfl, rfl⟩
    simp [FOBall.ext_iff, neg_eq_of_add_eq_zero_right h]
  --TODO hide this instance, see above
  zsmul := zsmulRec

instance : SubNegZeroMonoid FOBall where
  neg_zero := by simp

instance : CommMonoid FOBall where
  one_mul _ := by simp [FOBall.ext_iff]
  mul_one _ := by simp [FOBall.ext_iff]
  mul_assoc _ _ _ := by
    simp [mul_def, mul_pow]
    use by ring, by ring
  mul_comm _ _ := by
    simpa [mul_def] using And.intro (mul_comm _ _) (add_comm _ _)
  --TODO hide this instance, see above
  npow := npowRec

noncomputable instance : DivInvOneMonoid FOBall where
  inv_one := by simp [FOBall.ext_iff]
  --TODO hide this instance, see above
  zpow := zpowRec

noncomputable instance : MulZeroOneClass FOBall where
  zero_mul _ := by simp [FOBall.ext_iff]
  mul_zero _ := by simp [FOBall.ext_iff]

instance : HasDistribNeg FOBall where
  neg_mul _ _ := by simp [FOBall.ext_iff]
  mul_neg _ _ := by simp [FOBall.ext_iff]

noncomputable instance : MinimalRing FOBall where

/-- The ring homomorphism from ℝ into FOBall (specifically, an isomorphism on the 0-width set.) -/
def pure : MinimalRingHom ℝ FOBall where
  toFun x := ⟨x, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_mul' := by simp [FOBall.ext_iff]
  map_add' := by simp [FOBall.ext_iff]

instance : Coe ℝ FOBall :=
  ⟨pure⟩

@[simp]
theorem mid_pure (x : ℝ) : (pure x).mid = x := by
  rfl

@[simp]
theorem var_pure (x : ℝ) : (pure x).var = 0 := by
  rfl

theorem pure_zero : pure 0 = 0 := by
  simp

theorem pure_one : pure 1 = 1 := by
  simp

@[simp]
theorem pure_natCast (n : ℕ) : pure n = n := by
  rfl

@[simp]
theorem pure_intCast (z : ℤ) : pure z = z := by
  rfl

@[simp]
theorem pure_ratCast (q : ℚ) : pure q = q := by
  rfl

theorem pure_add (x y : ℝ) : pure (x + y) = pure x + pure y := by
  simp only [map_add]

theorem pure_neg (x : ℝ) : pure (-x) = -pure x := by
  simp

theorem pure_sub (x y : ℝ) : pure (x - y) = pure x - pure y := by
  simp only [map_sub]

theorem pure_mul (x y : ℝ) : pure (x * y) = pure x * pure y := by
  simp only [map_mul]

@[simp]
theorem pure_inv (x : ℝ) : pure (x⁻¹) = (pure x)⁻¹ := by
  ext <;> simp

@[simp]
theorem pure_div (x y : ℝ) : pure (x / y) = pure x / pure y := by
  ext <;> simp

section ofScientific

def ofScientific (m : ℕ) (sign : Bool) (e : ℕ) : FOBall :=
  let e' := (if sign then -e else e : ℤ);
  ⟨(m * 10^e' : ℚ), ⟨(10^e' / 2 : ℚ)^2, sq_nonneg _⟩⟩

instance : OfScientific FOBall where
  ofScientific := ofScientific

@[simp]
theorem ofScientific_mid (m : ℕ) (sign : Bool) (e : ℕ) :
    (OfScientific.ofScientific m sign e : FOBall).mid =
      (m * 10^(if sign then -e else e : ℤ) : ℚ) := by
  rfl

@[simp]
theorem ofScientific_e (m : ℕ) (sign : Bool) (e : ℕ) :
    (OfScientific.ofScientific m sign e : FOBall).var =
      ⟨(10^(if sign then -e else e : ℤ) / 2 : ℚ)^2, sq_nonneg _⟩ := by
  rfl

end ofScientific

/-- The `a ± b` notation parses as `p` with `p.mid = a` and `p.var = b^2`. -/
scoped macro n:term "±" pm:term : term => `((⟨$n, ⟨$pm ^ 2, sq_nonneg $pm⟩⟩ : FOBall))

section setlike

/-- Interpreting an `FOBall` as a confidence interval, is the given value
`x` consistent with it? -/
def mem (r : FOBall) (x : ℝ) : Prop :=
  (x - r.mid)^2 ≤ r.var

instance : SetLike FOBall ℝ where
  coe r := setOf r.mem
  coe_injective' r s h := by
    simp [Set.ext_iff, mem] at h
    rcases lt_trichotomy (r.mid + √r.var) (s.mid + √s.var) with h₂ | h₂ | h₂
    rotate_left
    · rcases lt_trichotomy (r.mid - √r.var) (s.mid - √s.var) with h₂ | h₂ | h₂
      rotate_left
      · have hm : r.mid = s.mid := by linarith
        have hv : √r.var = √s.var := by linarith
        rw [Real.sqrt_inj (by positivity) (by positivity), ← NNReal.eq_iff] at hv
        simp [hm, hv, FOBall.ext_iff]
      · exfalso
        specialize h (s.mid - √s.var)
        simp only [sub_sub_cancel_left, even_two, Even.neg_pow, zero_le_coe,
          Real.sq_sqrt, le_refl, iff_true] at h
        rw [← one_mul (_^2), ← neg_one_sq, ← mul_pow, neg_mul] at h
        rw [← Real.le_sqrt' (by linarith [Real.sqrt_nonneg r.var])] at h
        linarith
      · exfalso
        specialize h (r.mid - √r.var)
        simp only [sub_sub_cancel_left, even_two, Even.neg_pow, zero_le_coe,
          Real.sq_sqrt, le_refl, true_iff] at h
        rw [← one_mul (_^2), ← neg_one_sq, ← mul_pow, neg_mul] at h
        rw [← Real.le_sqrt' (by linarith [Real.sqrt_nonneg r.var])] at h
        linarith
    · exfalso
      specialize h (r.mid + √r.var)
      simp at h
      rw [← Real.le_sqrt' (by linarith [Real.sqrt_nonneg s.var])] at h
      linarith
    · exfalso
      specialize h (s.mid + √s.var)
      simp at h
      rw [← Real.le_sqrt' (by linarith [Real.sqrt_nonneg r.var])] at h
      linarith

theorem mem_def (r : FOBall) (x : ℝ) : x ∈ r ↔ (x - r.mid)^2 ≤ r.var := by
  rfl

section map

--For Mathlib
section lipschitzAt
open Topology

def LipschitzAtFilter {X Y : Type*} [EDist X] [EDist Y]
    (f : X → Y) (l : Filter (X × X)) : Prop :=
  ∃ (C : NNReal), ∀ᶠ z in l, edist (f z.1) (f z.2) ≤ C * edist z.1 z.2

def LipschitzWithAtFilter {X Y : Type*} [EDist X] [EDist Y]
    (C : NNReal) (f : X → Y) (l : Filter (X × X)) : Prop :=
  ∀ᶠ z in l, edist (f z.1) (f z.2) ≤ C * edist z.1 z.2

def LipschitzAt {X Y : Type*} [TopologicalSpace X] [EDist X] [EDist Y]
    (f : X → Y) (p : X) : Prop :=
  ∃ (C : NNReal), ∀ᶠ z in 𝓝 p , edist (f z) (f p) ≤ C * edist z p

def LipschitzWithAt {X Y : Type*} [TopologicalSpace X] [EDist X] [EDist Y]
    (C : NNReal) (f : X → Y) (p : X) : Prop :=
  ∀ᶠ z in 𝓝 p , edist (f z) (f p) ≤ C * edist z p

/-- The infimum of constants C so that `f` is C-Lipschitz on the filter `l`. -/
noncomputable def lipschitzAt {X Y : Type*} [TopologicalSpace X] [EDist X] [EDist Y]
    (f : X → Y) (p : X) : NNReal :=
  sInf {C | LipschitzWithAt C f p}

theorem LipschitzWithAt.lipschitzAt {X Y : Type*} [TopologicalSpace X] [EDist X] [EDist Y]
    {C : NNReal} {f : X → Y} {p : X} (hf : LipschitzWithAt C f p) : LipschitzAt f p :=
  ⟨C, hf⟩

@[simp]
theorem _root_.DifferentiableAt.LipschitzAt {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    LipschitzAt f x := by
  obtain ⟨w, h⟩ : ∃ C : ℝ, ∀ᶠ z in 𝓝 x, |f z - f x| ≤ C * |z - x| := by
    -- Since f is differentiable at x, we have lim_{z → x} (f(z) - f(x)) / (z - x) = f'(x).
    have h_deriv : (𝓝[≠] x).Tendsto (fun z => (f z - f x) / (z - x)) (𝓝 (deriv f x)) := by
      simpa [hasDerivAt_iff_tendsto_slope, div_eq_inv_mul] using hf.hasDerivAt
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ᶠ z in (𝓝[≠] x), |(f z - f x) / (z - x)| ≤ C :=
      ⟨_, h_deriv.abs.eventually (ge_mem_nhds <| lt_add_one _)⟩
    -- Since |(f z - f x) / (z - x)| ≤ C for z ≠ x, multiplying both sides by |z - x| gives
    -- |f z - f x| ≤ C * |z - x| for z ≠ x. For z = x, |f z - f x| = 0 ≤ C * |z - x| trivially.
    use C
    have hl : ∀ᶠ z in 𝓝 x, z ≠ x → |f z - f x| ≤ C * |z - x| := by
      rw [eventually_nhdsWithin_iff] at hC
      filter_upwards [hC] with z hz hzx
      simpa only [abs_div, div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hzx))] using hz hzx
    filter_upwards [hl] with z hz using if h : z = x then by simp [h] else hz h
  use ⟨|w|, by positivity⟩
  filter_upwards [h] with z hz
  apply ENNReal.coe_le_coe.mpr
  simpa [abs_mul] using hz.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _))

/-- For differentiable functions, the lipschitz constant at a point is the absolute
value of the derivative. -/
@[simp]
theorem _root_.DifferentiableAt.lipschitzAt_eq_deriv {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    lipschitzAt f x = ‖deriv f x‖₊ := by
  simp only [NNReal.eq_iff, coe_nnnorm, Real.norm_eq_abs]
  have h_C_lipschitz : ∀ (C : NNReal), C > |deriv f x| → LipschitzWithAt C f x := by
    have h_deriv : (𝓝[≠] x).Tendsto (fun z ↦ (f z - f x) / (z - x)) (𝓝 (deriv f x)) := by
      simpa [hasDerivAt_iff_tendsto_slope, div_eq_inv_mul] using hf.hasDerivAt
    intro C hC
    have h_bound : ∀ᶠ z in 𝓝[≠] x, |(f z - f x) / (z - x)| ≤ C :=
      h_deriv.abs.eventually (ge_mem_nhds hC)
    rw [eventually_nhdsWithin_iff] at h_bound
    filter_upwards [h_bound] with y hy
    by_cases h : y = x
    · simp [h]
    simp [edist_dist, abs_div] at hy ⊢
    rw [div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr h))] at hy
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)]
    exact hy h
  apply le_antisymm
  · by_contra h_contra
    obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, |deriv f x| < C ∧ C < lipschitzAt f x :=
      ⟨⟨(|deriv f x| + lipschitzAt f x) / 2, by positivity⟩,
        by norm_num; linarith,
        NNReal.coe_lt_coe.mp (by norm_num; linarith)⟩
    exact hC.2.not_ge <| csInf_le ⟨0, fun C hC ↦ by positivity⟩ <| h_C_lipschitz C hC.1
  · -- Suppose C < |f'(x)|. We need to show that f is not C-Lipschitz at x.
    have h_not_C_lipschitz : ∀ (C : ℝ≥0), C < |deriv f x| → ¬LipschitzWithAt C f x := by
      intro C hC_lt
      by_contra h_contra
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ y, |y - x| < ε → |f y - f x| ≤ C * |y - x| := by
        rcases Metric.mem_nhds_iff.mp h_contra with ⟨ε, ε_pos, hε⟩;
        use ε, ε_pos
        simp_all [edist_dist]
        intro y hy
        specialize hε hy
        rw [Set.mem_setOf_eq, ENNReal.ofReal_le_iff_le_toReal] at hε
        · simpa [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.dist_eq,
            ENNReal.toReal_ofReal (abs_nonneg _)] using hε
        · simp_all [ENNReal.mul_eq_top]
      have h_lim : (𝓝[≠] x).Tendsto (fun y ↦ |(f y - f x) / (y - x)|) (𝓝 |deriv f x|) := by
        have hd := hf.hasDerivAt
        rw [hasDerivAt_iff_tendsto_slope] at hd
        simpa [div_eq_inv_mul] using hd.abs
      have h_lim_le : ∀ᶠ y in (𝓝[≠] x), |(f y - f x) / (y - x)| ≤ C := by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hε_pos)] with y hy hy'
        rw [abs_div]
        exact div_le_of_le_mul₀ (abs_nonneg _) (by positivity) (hε y hy')
      exact hC_lt.not_ge <| le_of_tendsto h_lim h_lim_le;
    refine' le_of_not_gt fun h ↦ _;
    -- By definition of infimum, if the infimum is less than |deriv f x|, there exists some C in the
    -- set such that C < |deriv f x|.
    obtain ⟨C, hC₁, hC₂⟩ : ∃ C : ℝ≥0, LipschitzWithAt C f x ∧ C < |deriv f x| := by
      have h_inf : ∀ ε > 0, ∃ C : ℝ≥0, LipschitzWithAt C f x ∧ C < lipschitzAt f x + ε := by
        intro ε ε_pos
        exact exists_lt_of_csInf_lt (show {C : ℝ≥0 | LipschitzWithAt C f x}.Nonempty from
          ⟨_, h_C_lipschitz (⟨|deriv f x| + 1, by positivity⟩ : ℝ≥0) (by norm_num)⟩)
            (lt_add_of_pos_right _ ε_pos)
      obtain ⟨C, hC⟩ := h_inf (⟨|deriv f x| - lipschitzAt f x, sub_nonneg.2 h.le⟩) (sub_pos.2 h)
      use C, hC.1
      linarith [show C < lipschitzAt f x + (|deriv f x| - lipschitzAt f x) from mod_cast hC.2]
    tauto

theorem _root_.LipschitzWithAt_one_abs {x : ℝ} : LipschitzWithAt 1 abs x := by
  simp [LipschitzWithAt, edist_dist, Real.dist_eq]
  exact Filter.Eventually.of_forall (abs_abs_sub_abs_le_abs_sub · x)

@[simp]
theorem _root_.abs_lipschitzAt {x : ℝ} : lipschitzAt abs x = 1 := by
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) LipschitzWithAt_one_abs
  · apply le_csInf LipschitzWithAt_one_abs.lipschitzAt
    intro b hb
    have h_lip : ∀ᶠ z in 𝓝 x, |abs z - abs x| ≤ b * |z - x| := by
      convert hb using 1
      simp [EDist.edist, PseudoMetricSpace.edist_dist, ENNReal.ofReal, Real.dist_eq]
      norm_cast
    contrapose! h_lip
    field_simp [Metric.eventually_nhds_iff]
    intro ε ε_pos
    rcases lt_or_ge 0 x with hx | hx
    -- Choose y = x ± ε/2
    · use x + ε / 2
      norm_num [abs_of_pos, hx, ε_pos]
      rw [abs_of_nonneg]
      <;> cases abs_cases (x + ε / 2)
      <;> nlinarith [show (b : ℝ) < 1 from h_lip]
    · use x - ε / 2
      simp
      use by linarith [abs_of_pos ε_pos]
      cases abs_cases (x - ε / 2)
      <;> cases abs_cases x
      <;> cases abs_cases (|x - ε / 2| - |x|)
      <;> nlinarith [abs_of_pos (half_pos ε_pos), show (b : ℝ) < 1 from h_lip]

end lipschitzAt

/-- Map a value forward through a real function. If the real function isn't
differentiable at a point, then we get the dummy value 0 for the uncertainty. -/
@[irreducible]
noncomputable def map (f : ℝ → ℝ) (x : FOBall) : FOBall :=
  ⟨f x.mid,
    open Classical in
    if LipschitzAt f x.mid then (lipschitzAt f x.mid)^2 * x.var else 0⟩

@[simp]
theorem map_mid (f : ℝ → ℝ) (x : FOBall) : (map f x).mid = f x.mid := by
  simp [map]

@[simp]
theorem map_pure (f : ℝ → ℝ) (x : ℝ) : map f (pure x) = ⟨f x, 0⟩ := by
  ext <;> simp [map]

theorem map_differentiableAt (f : ℝ → ℝ) (x : FOBall) (hf : DifferentiableAt ℝ f x.mid) :
    map f x = ⟨f x.mid, ⟨(deriv f x.mid)^2, sq_nonneg _⟩ * x.var⟩ := by
  rw [map, if_pos hf.LipschitzAt, hf.lipschitzAt_eq_deriv]
  simp only [mk.injEq, mul_eq_mul_right_iff, true_and]
  left; ext; simp

@[simp]
theorem map_differentiable (f : ℝ → ℝ) (x : FOBall) (hf : Differentiable ℝ f) :
    map f x = ⟨f x.mid, ⟨(deriv f x.mid)^2, sq_nonneg _⟩ * x.var⟩ :=
  map_differentiableAt f x hf.differentiableAt

@[simp]
theorem map_abs (x : FOBall) :
    map abs x = ⟨abs x.mid, x.var⟩ := by
  simp [map, LipschitzWithAt_one_abs.lipschitzAt]

noncomputable scoped instance : FunLike (ℝ → ℝ) FOBall FOBall where
  coe f := FOBall.map f
  coe_injective' _ _ h := by
    funext x
    simpa using congrFun h x

/-- This simp lemma, arguably, makes things slightly harder to read: a simple coercion
is turned into a `map f`. But frequently enough, I expect, the implicitness of this
could confuse the reader, and make copying claims (e.g. for a `have`) harder. In this
case, it seems better to encourage explicitness of the cast. -/
@[simp]
theorem funLike_eq_map (f : ℝ → ℝ) : (⇑f : FOBall → FOBall) = map f := by
  rfl

end map

section approx

/-- **Approximate equality of FOBalls**. See `ℝRange.isApprox` for some elaboration
on what this means, what it doesn't, and why this definition was chosen. -/
def isApprox (x y : FOBall) : Prop :=
  |x.mid - y.mid| ≤ √x.var + √y.var ∧ y.var ≤ 16 * x.var ∧ x.var ≤ 16 * y.var

instance : HasEquiv FOBall :=
  ⟨isApprox⟩

/-- The provided definition of `isApprox`, which is most directly comparable to
`ℝRange.isApprox`. -/
theorem isApprox_def (x y : FOBall) : x ≈ y ↔
    |x.mid - y.mid| ≤ √x.var + √y.var ∧ y.var ≤ 16 * x.var ∧ x.var ≤ 16 * y.var := by
  rfl

/-- A logically equivalent definition of `isApprox` that avoids square roots, more
amenable to numerical verification. -/
@[simp]
theorem isApprox_iff (x y : FOBall) : x ≈ y ↔
    (|x.mid - y.mid|^2 ≤ x.var + y.var ∨
      (|x.mid - y.mid|^2 - x.var - y.var)^2 ≤ 4 * x.var * y.var) ∧
      (y.var ≤ 16 * x.var ∧ x.var ≤ 16 * y.var) := by
  rw [isApprox_def, and_congr_left_iff]
  intro _
  congr!
  constructor
  · intro h
    by_cases h₂ : |x.mid - y.mid| ^ 2 ≤ x.var + y.var
    · exact .inl h₂
    push_neg at h₂
    rcases x with ⟨xm, xv⟩
    rcases y with ⟨ym, yv⟩
    dsimp at h h₂ ⊢
    -- Since $|xm - ym| ≤ √xv + √yv, squaring both sides gives |xm - ym|^2 ≤ (√xv + √yv)^2.
    have h_sq : |xm - ym|^2 ≤ (√xv + √yv)^2 := by gcongr
    -- If $|xm - ym|^2 > xv + yv$, then $|xm - ym|^2 - xv - yv \leq 2\sqrt{xv yv}$.
    have h_diff : |xm - ym|^2 - xv - yv ≤ 2 * √(xv * yv) := by
      rw [Real.sqrt_mul xv.zero_le_coe]
      nlinarith [Real.mul_self_sqrt xv.zero_le_coe, Real.mul_self_sqrt yv.zero_le_coe]
    -- Squaring both sides of $|xm - ym|^2 - xv - yv \leq 2\sqrt{xv yv}$, we get $(|xm - ym|^2 - xv - yv)^2 \leq 4xv yv$.
    have h_diff_sq := pow_le_pow_left₀ (by linarith) h_diff 2
    refine .inr (h_diff_sq.trans ?_)
    nlinarith only [Real.mul_self_sqrt (mul_nonneg xv.coe_nonneg yv.coe_nonneg)]
  · rcases x with ⟨xm, xv⟩
    rcases y with ⟨ym, yv⟩
    dsimp
    rintro (h_case1 | h_case2)
    · nlinarith [Real.sqrt_nonneg xv, Real.mul_self_sqrt xv.zero_le_coe,
        Real.sqrt_nonneg yv, Real.mul_self_sqrt yv.zero_le_coe]
    · -- Taking the square root of both sides of the inequality
      have h_sqrt_case2 : |xm - ym|^2 ≤ xv + yv + 2 * Real.sqrt (xv * yv ) := by
        nlinarith [Real.sqrt_nonneg (xv * yv), Real.mul_self_sqrt (by positivity : 0 ≤ (xv : ℝ) * yv)]
      rw [Real.sqrt_mul (by positivity)] at h_sqrt_case2
      nlinarith only [h_sqrt_case2, Real.sqrt_nonneg xv, Real.sqrt_nonneg yv,
        Real.mul_self_sqrt xv.coe_nonneg, Real.mul_self_sqrt yv.coe_nonneg]

instance : IsRefl FOBall (· ≈ ·) where
  refl x := by simp [← NNReal.coe_le_coe]; linarith [x.var.coe_nonneg]

instance : IsSymm FOBall (· ≈ ·) where
  symm x y h := by
    rw [isApprox_iff] at h ⊢
    convert h using 1
    · congr! 2
      · rw [abs_sub_comm]
      · exact add_comm _ _
      · rw [abs_sub_comm]
        ring_nf
      · ring_nf
    · tauto

end approx
