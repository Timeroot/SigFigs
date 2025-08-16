import Mathlib.Analysis.RCLike.Basic

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
Here the justification is given on each line. The error between the two is highlighted in the middle,
an error of `2 V[X] 𝔼[Y] 𝔼[Z]` higher variance on `V[X(Y+Z)]`. And each step alone is justified
appropriately (treating X/Y/Z as independent variables), except for the line
`(true when XY vs. XZ independent)`, when clearly is not realistically true. Then the corrected formula
would be,
```
V[XY + XZ] =
V[XY] + V[XZ] + 2Cov[XY, XZ]
```
where the covariance term is
```
Cov[XY, XZ] =
𝔼[(XY)(XZ)] - 𝔼[XY] 𝔼[XZ] =
𝔼[X²YZ] - 𝔼[XY] 𝔼[XZ] =
𝔼[X²] 𝔼[Y] 𝔼[Z] - (𝔼[X] 𝔼[Y]) (𝔼[X] 𝔼[Z]) =
(𝔼[X²] - 𝔼[X]^2) 𝔼[Y] 𝔼[Z] =
V[X] 𝔼[Y] 𝔼[Z]
```
as expected. By treating the errors in `XY` and `XZ` as independent, instead of appropriately correlated,
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

--TODO: simps for NatCast / IntCast / RatCast

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

/-- To give `FOBall.pure` a nice ring homomorphism structure manifestly, we'd like to give it a `RingHom`
type. But, that would require actually having a `Ring` of some sort, which we don't, sad. So, we define
an exact alias of it (with weaker requirements) here.

Unfortunately -- such a type requires an `AddZeroClass` structure and a `MulZeroOneClass`
structure. The unique common ancestor of these is `NonAssocSemiring`, which again, we don't have. And
if we give them individually, then we have multiple definitions of `Zero` - neither of these exist
as mixins. So, we need to define a new class for this.
-/
class MinimalRing (β : Type*) extends AddZeroClass β, MulZeroOneClass β

instance (β : Type*) [NonAssocSemiring β] : MinimalRing β where

structure MinimalRingHom (α : Type*) (β : Type*) [MinimalRing α] [MinimalRing β] extends
  α →* β, α →+ β, α →ₙ* β, α →*₀ β

section MinimalRingHomClass

class MinimalRingHomClass (F : Type*) (α β : outParam Type*)
    [MinimalRing α] [MinimalRing β] [FunLike F α β] : Prop
  extends MonoidHomClass F α β, AddMonoidHomClass F α β, MulHomClass F α β, MonoidWithZeroHomClass F α β

variable {F α β : Type*} [FunLike F α β]

@[coe]
def MinimalRingHomClass.toMinimalRingHom {_ : MinimalRing α} {_ : MinimalRing β} [MinimalRingHomClass F α β]
    (f : F) : MinimalRingHom α β :=
  { (f : α →* β), (f : α →+ β) with }

instance {_ : MinimalRing α} {_ : MinimalRing β} [MinimalRingHomClass F α β] :
    CoeTC F (MinimalRingHom α β) :=
  ⟨MinimalRingHomClass.toMinimalRingHom⟩

instance MinimalRingHomClass.toRingHomClass [NonAssocSemiring α] [NonAssocSemiring β]
    [MinimalRingHomClass F α β] : RingHomClass F α β :=
  { ‹MinimalRingHomClass F α β› with }

end MinimalRingHomClass

namespace MinimalRingHom

/-!
Throughout this section, some `Semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/

variable [MinimalRing α] [MinimalRing β]

instance instFunLike : FunLike (MinimalRingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance : MinimalRingHomClass (MinimalRingHom α β) α β where
  map_add := MinimalRingHom.map_add'
  map_zero := MinimalRingHom.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections MinimalRingHom (toFun → apply)

end MinimalRingHom

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
  sorry

@[simp]
theorem pure_div (x y : ℝ) : pure (x / y) = pure x / pure y := by
  sorry
