import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.RCLike.Basic

/-- A `ℝRange` for a range of possible real values associated to a quantity with uncertainty. It's
a `NonemptyInterval ℝ`, but we give it some other useful instances. -/
abbrev ℝRange := NonemptyInterval ℝ

noncomputable section
namespace ℝRange

abbrev pure : ℝ → ℝRange := NonemptyInterval.pure

instance : Coe ℝ ℝRange := ⟨pure⟩

instance : AddCommMonoid ℝRange :=
  inferInstance

instance : SubtractionCommMonoid ℝRange :=
  inferInstance

instance : One ℝRange :=
  inferInstance

instance : NatCast ℝRange :=
  inferInstance

instance : IntCast ℝRange :=
  ⟨(pure ·)⟩

instance : RatCast ℝRange :=
  ⟨(pure ·)⟩

instance : Membership ℝ ℝRange :=
  inferInstance

@[simp]
theorem toProd_zero :
    (NonemptyInterval.toProd (0 : ℝRange)) = (0, 0) := by
  rfl

@[simp]
theorem toProd_one :
    (NonemptyInterval.toProd (1 : ℝRange)) = (1, 1) := by
  rfl

@[simp]
theorem toProd_ofNat (n : ℕ) [n.AtLeastTwo] :
    (NonemptyInterval.toProd (ofNat(n) : ℝRange)) = ((n : ℝ), (n : ℝ)) := by
  rfl

--See https://github.com/Timeroot/ComputableReal/blob/61221e0d67648119919bc51b27e693766f48c791/ComputableReal/ComputableRSeq.lean#L13C37-L23C1
/--Multiplication on intervals of ℚ. TODO: Should generalize to any LinearOrderedField... -/
def mul_pair (x y : ℝRange) : ℝRange :=
  let ⟨⟨xl,xu⟩,_⟩ := x
  let ⟨⟨yl,yu⟩,_⟩ := y
  ⟨⟨min (min (xl*yl) (xu*yl)) (min (xl*yu) (xu*yu)),
    max (max (xl*yl) (xu*yl)) (max (xl*yu) (xu*yu))⟩,
    by simp only [le_max_iff, min_le_iff, le_refl, true_or, or_true, or_self]⟩

-- /--Multiplication of intervals by a ℚ. TODO: Should generalize to any LinearOrderedField -/
-- def mul_pure (x : ℝRange) (y : ℝ) : ℝRange :=
--   if h : y ≥ 0 then
--     ⟨⟨x.fst * y, x.snd * y⟩, mul_le_mul_of_nonneg_right x.2 h⟩
--   else
--     ⟨⟨x.snd * y, x.fst * y⟩, (mul_le_mul_right_of_neg (lt_of_not_ge h)).mpr x.2⟩

instance : Mul ℝRange :=
  ⟨mul_pair⟩

-- instance : HMul ℝRange ℝ ℝRange :=
--   ⟨mul_pure⟩

-- instance : HDiv ℝRange ℝ ℝRange :=
--   ⟨fun x y ↦ x * y⁻¹⟩

/-- The **inverse** of an interval. We take, as a junk value, that if 0 is in the interval,
then the inverse is the unique number 0. Otherwise, it's `[1/snd, 1/fst]` as one would expect. -/
instance : Inv ℝRange :=
  open Classical in
  ⟨fun x ↦ if h : 0 ∈ x then 0 else ⟨(x.snd⁻¹, x.fst⁻¹), sorry⟩⟩

instance : Div ℝRange :=
  ⟨fun x y ↦ x * y⁻¹⟩

def natPow (x : ℝRange) (n : ℕ) : ℝRange :=
  if h : Even n then
    let lb := min (abs x.fst) (abs x.snd);
    let ub := max (abs x.fst) (abs x.snd);
    ⟨(lb ^ n, ub ^ n), sorry⟩
  else
    ⟨⟨x.fst ^ n, x.snd ^n⟩, sorry⟩

instance : NatPow ℝRange :=
  ⟨natPow⟩

theorem mul_fst (x y : ℝRange) : (x * y).fst =
    let ⟨⟨xl,xu⟩,_⟩ := x; let ⟨⟨yl,yu⟩,_⟩ := y; min (min (xl*yl) (xu*yl)) (min (xl*yu) (xu*yu)) := by
  rfl

theorem mul_snd (x y : ℝRange) : (x * y).snd =
    let ⟨⟨xl,xu⟩,_⟩ := x; let ⟨⟨yl,yu⟩,_⟩ := y; max (max (xl*yl) (xu*yl)) (max (xl*yu) (xu*yu)) := by
  rfl

instance : CommMagma ℝRange where
  mul_comm := by
    rintro ⟨⟨a₁,a₂⟩, _⟩ ⟨⟨b₁,b₂⟩, _⟩
    ext
    · simp [mul_fst, min_assoc, mul_comm b₁ _, mul_comm b₂ _]
      congr 1
      rw [← min_assoc, ← min_assoc, min_comm (_ * _)]
    · simp [mul_snd, max_assoc, mul_comm b₁ _, mul_comm b₂ _]
      congr 1
      rw [← max_assoc, ← max_assoc, max_comm (_ * _)]

instance : MulZeroOneClass ℝRange where
  one_mul a := by
    ext <;> simp [mul_fst, mul_snd, a.2]
  mul_one a := by
    ext <;> simp [mul_fst, mul_snd, a.2]
  zero_mul a := by
    ext <;> simp [mul_fst, mul_snd]
  mul_zero a := by
    ext <;> simp [mul_fst, mul_snd]

-- TODO
-- instance : IsCancelMulZero ℝRange where
--   mul_left_cancel_of_ne_zero := sorry
--   mul_right_cancel_of_ne_zero := sorry

def ofScientific (m : ℕ) (sign : Bool) (e : ℕ) : ℝRange :=
  let e' := (if sign then -e else e : ℤ) - 1;
  ⟨⟨(10 * m - 5) * 10^e', (10 * m + 5) * 10^e'⟩, by
    simp [add_assoc, zpow_pos (a := (10 : ℝ)) Nat.ofNat_pos' e']⟩

instance : OfScientific ℝRange where
  ofScientific := ofScientific

@[simp]
theorem ofScientific_fst (m : ℕ) (sign : Bool) (e : ℕ) :
  (OfScientific.ofScientific m sign e : ℝRange).fst =
    (10 * m - 5) * 10^((if sign then -e else e : ℤ) - 1) := by
  rfl

@[simp]
theorem ofScientific_snd (m : ℕ) (sign : Bool) (e : ℕ) :
  (OfScientific.ofScientific m sign e : ℝRange).snd =
    (10 * m + 5) * 10^((if sign then -e else e : ℤ) - 1) := by
  rfl

--This means that the literal `1.23` now elaborates as the range `[1.225, 1.235]`, in accordance
--with typical scientific notation
example : (1.23 : ℝRange) = ⟨⟨1.225, 1.235⟩, by norm_num⟩ := by
  ext <;> norm_num

macro n:term "ₑₓ" : term => `(pure $n)

macro n:term "ᵤ" : term => `(($n : ℝRange))

@[app_unexpander ℝRange.pure] meta def unexpandPureScientific : Lean.PrettyPrinter.Unexpander
  | `($_ $tail) =>
    match Lean.Syntax.isScientificLit? tail with
    | some _ => `($tail ₑₓ)
    | _          => `(↑$tail)
  | _ => throw ()

macro n:term "±" pm:term : term => `((⟨⟨$n - $pm, $n + $pm⟩, by linarith⟩ : ℝRange))

@[app_unexpander NonemptyInterval.mk] meta def unexpandPlusMinus : Lean.PrettyPrinter.Unexpander
  | `($_ ($a - $b, $c + $d) $_) => (if a == c && b == d then `($a±$b) else throw ())
  | _ => throw ()

/-- **Approximate equality of intervals**. We say that two intervals are equivalent, `≈`, if
they overlap and their widths are at most a factor of 4 apart. Why 4? Because 4 is the ceiling
of √10, so -- if the right hand side is the left hand side rounded off to the nearest integer
number of significant figures -- then it will be consistent. We could use √10 instead, but this
is will almost always make calculations much more of a pain, because we introduce an irrational
quantity.

This is a symmetric and reflexive relation, but not a transitive one.
-/
def isApprox (x y : ℝRange) : Prop :=
  (x.fst ≤ y.snd ∧ y.fst ≤ x.snd) ∧
  (y.snd - y.fst ≤ 4 * (x.snd - x.fst) ∧ x.snd - x.fst ≤ 4 * (y.snd - y.fst))

instance : HasEquiv ℝRange :=
  ⟨isApprox⟩

@[simp]
theorem isApprox_iff (x y : ℝRange) : x ≈ y ↔
    (x.fst ≤ y.snd ∧ y.fst ≤ x.snd) ∧
    (y.snd - y.fst ≤ 4 * (x.snd - x.fst) ∧ x.snd - x.fst ≤ 4 * (y.snd - y.fst)) := by
  rfl

instance : IsRefl ℝRange (· ≈ ·) where
  refl x := by
    simp [x.2]
    linarith [x.2]

instance : IsSymm ℝRange (· ≈ ·) where
  symm x y := by
    simp; intros
    and_intros <;> linarith
