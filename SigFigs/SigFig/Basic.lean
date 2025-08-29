import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum.NatLog

/-! # The "Significant Figures" model of uncertainty tracking

In this model, numbers are stored as a finite-length decimal string, with an implied uncertainty
in the last digit. That is, there is a fixed and integer number of "significant figures", and
precisely that much information is stored.

When numbers are added, the less precise of the two (in absolute units) is used; when multiplied,
the less precise of the two (in relative precision, that is, string length) is used. This is
convenient for pocket-calculator or even mental calculations, where storing a single (typically
short) string is much easier than tracking a long and messy decimal _and_ its uncertainty
separately. Accordingly, it is a commonly used method of uncertainty tracking in grade school
and some lower-level undergrad courses. But it is quite uncommon in professional work where,
presumably, computers are available which can track the intermediate calculations appropriately.
That said, many professionals employ some version of this system during conversation for quick
ballpark estimates.

As a mathematical structure, it enjoys relatively few nice properties. Computations are generally
commutative, and addition is associative when all inputs have the same precision, but generally
addition is not associative; multiplication is almost never associative, not even power-associative.
Multiplication even by an exact real number is not invertible.

Interally, we model numbers similar to `OfScientific`, in a floating-point format: an integer
mantissa and an integer exponent. Exact real numbers such `37`, `9 / 16` or `π` have no reasonable
representation in this system (they only acquire a precision when used with a limited-precision
number), which we handle by appropriate `HAdd` and `HMul` instances. Sadly, this leads to some
code duplication.

Accordingly, there is also no value of "0" or "1". But this is not as big as an issue as one
would think, because essentially every instances where this would occur it occurs as an exact
real number, and this gets used in the approate `HAdd` or `HMul` instance.
-/

/-- A number with given significant figures, interpretable as a rational with value `m * 10^e`
and uncertainty in the last digit - suggesting an interval `[m - 1/2, m + 1/2] * 10^e`. -/
@[ext]
structure SigFig where
  m : ℤ
  e : ℤ
deriving DecidableEq

namespace SigFig

variable (r s : SigFig) (x y : ℝ) (e : ℤ)

section rounding


/-- Round a SigFig to a given precision. Rounding is done with `round`, which always
rounds `n + 1/2` to `n + 1`. This is not generally a sensible function to use unless
`s.e < e`, as otherwise you are "increasing the precision" of a number. -/
nonrec def roundTo (s : SigFig) (e : ℤ) : SigFig where
  m := round (s.m * 10 ^ (s.e - e) : ℚ)
  e := e

theorem roundTo_m (s : SigFig) (e : ℤ) : (s.roundTo e).m = round (s.m * 10 ^ (s.e - e) : ℚ) := by
  rfl

@[simp]
theorem roundTo_e (s : SigFig) (e : ℤ) : (s.roundTo e).e = e := by
  rfl

@[simp]
theorem roundTo_self (s : SigFig) : (s.roundTo s.e) = s := by
  simp [roundTo]

@[simp]
def toRat (s : SigFig) : ℚ :=
  s.m * 10 ^ s.e

/-- Convert a real number to a `SigFig` at a given level of precision. Uses `round`, which rounds
half-integers up. -/
noncomputable def ofReal (x : ℝ) (e : ℤ) : SigFig where
  m := round (x * 10 ^ e)
  e := e

theorem ofReal_m : (ofReal x e).m = round (x * 10 ^ e) := by
  rfl

@[simp]
theorem ofReal_e : (ofReal x e).e = e := by
  rfl

@[simp]
theorem toRat_ofReal (x : ℝ) : (ofReal x 0).toRat = round x := by
  simp [ofReal]

end rounding

section ofScientific

def ofScientific (m : ℕ) (sign : Bool) (e : ℕ) : SigFig :=
  ⟨m, if sign then -e else e⟩

instance : OfScientific SigFig where
  ofScientific := ofScientific

@[simp]
theorem ofScientific_m (m : ℕ) (sign : Bool) (e : ℕ) :
    (OfScientific.ofScientific m sign e : SigFig).m = m := by
  rfl

@[simp]
theorem ofScientific_e (m : ℕ) (sign : Bool) (e : ℕ) :
    (OfScientific.ofScientific m sign e : SigFig).e = (if sign then -e else e : ℤ) := by
  rfl

end ofScientific

section add

def add (r s : SigFig) : SigFig where
  m := round (r.m * 10 ^ (r.e - (max r.e s.e)) + s.m * 10 ^ (s.e - (max r.e s.e)) : ℚ)
  e := max r.e s.e

instance : Add SigFig :=
  ⟨add⟩

theorem add_def_m : (r + s).m =
    round (r.m * 10 ^ (r.e - (max r.e s.e)) + s.m * 10 ^ (s.e - (max r.e s.e)) : ℚ) := by
  rfl

@[simp]
theorem add_def_e : (r + s).e = max r.e s.e := by
  rfl

theorem add_def : r + s =
    let e' := max r.e s.e;
    ⟨(roundTo r e').m + (roundTo s e').m, e'⟩ := by
  ext
  · rcases max_cases r.e s.e with ⟨h₁, _⟩ | ⟨h₁, _⟩
    <;> simp [add_def_m, h₁, roundTo_m]
  · rfl

instance : AddCommMagma SigFig where
  add_comm r s := by simp [add_def, max_comm r.e s.e, add_comm]

noncomputable def hAdd (r : SigFig) (x : ℝ) : SigFig :=
  r + ofReal x r.e

noncomputable abbrev hAdd' (x : ℝ) (r : SigFig) : SigFig :=
  ofReal x r.e + r

@[simp]
theorem hAdd'_eq_hAdd : hAdd' x r = hAdd r x :=
  add_comm _ _

scoped notation:65 r " + " x:64 => hAdd r x
scoped notation:65 x " + " r:64 => hAdd' x r

theorem hAdd_real_def : r + x = r + ofReal x r.e := by
  rfl

@[simp]
theorem hAdd_real_e : (r + x).e = r.e := by
  simp [hAdd_real_def]

@[simp]
theorem add_zero : r + (0 : ℝ) = r := by
  simp [hAdd_real_def, SigFig.ext_iff, add_def_m, ofReal_m]

theorem zero_add : (0 : ℝ) + r = r := by
  simp

end add

section sub_neg

instance : Neg SigFig :=
  ⟨fun x ↦ ⟨-x.m, x.e⟩⟩

theorem neg_def (x : SigFig) : -x = ⟨-x.m, x.e⟩ := by
  rfl

@[simp]
theorem neg_m (x : SigFig) : (-x).m = -x.m := by
  rfl

@[simp]
theorem neg_e (x : SigFig) : (-x).e = x.e := by
  rfl

instance : InvolutiveNeg SigFig where
  neg_neg x := SigFig.ext (neg_neg x.m) rfl

instance : Sub SigFig :=
  ⟨fun x y ↦ x + (-y)⟩

theorem sub_def (x y : SigFig) : x - y = x + (-y) := by
  rfl

/-!
Due to the fact that rounding takes 3.5 to 4, but -3.5 to -3, we don't have the theorem
`-(ofReal x e) = ofReal (-x) e`. Also, when `x` and `y` are SigFigs, we don't have
`-(x + y) = -x + -y`. Accordingly, `-(x - y) = -(x + (-y)) ≠ -x + -(-y) = y + (-x) = y - x`.
In this sense, rounding towards/away from zero would be much cleaner axiomatically
speaking.

Well how do we define real subtraction? Either we define
```lean4
x - (y : ℝ) = x - ofReal y x.e
```
or
```lean4
x - (y : ℝ) = x + ofReal (-y) x.e
```
and these are inequivalent. Only the latter gets us `x - y = x + (-y)`, a version
of `sub_eq_add_neg`, so we adopt that.

We could define
```lean4
(x : ℝ) - y = ofReal x y.e - y
```
so that we get a version of `sub_eq_add_neg` again. Instead, to allow the simp-normal
form of putting reals together after, we define it as
```lean4
(x : ℝ) - y = -x + ofReal r x.e
```
so that `x - r` can be rewritten to `(-r) + x`.
-/


noncomputable def hSub (r : SigFig) (x : ℝ) : SigFig :=
  r + ofReal (-x) r.e

noncomputable abbrev hSub' (x : ℝ) (r : SigFig) : SigFig :=
   -r + ofReal x r.e

@[simp]
theorem hSub'_eq_hAdd : hSub' x r = hAdd (-r) x := by
  rfl

scoped notation:65 r " - " x:64 => hSub r x
scoped notation:65 x " - " r:64 => hSub' x r

theorem hSub_real_def : r - x = r + ofReal (-x) r.e := by
  rfl

theorem sub_real_eq_add_neg : r - x = r + (-x) := by
  rfl

@[simp]
theorem hSub_real_e : (r - x).e = r.e := by
  simp [sub_real_eq_add_neg]

theorem zero_sub : (0 : ℝ) - r = -r := by
  simp

@[simp]
theorem sub_zero : r - (0 : ℝ) = r := by
  rw [hSub, neg_zero]
  exact add_zero r

/-
Many other theorems you'd hope hold don't. We don't have
`(r + x) - x = r`, even when `x` is a real, or even an integer. We don't have
`-(x + y) = -x + -y`.
-/

end sub_neg

section mul

abbrev prec_int : ℤ → ℕ :=
  fun z ↦ if z = 0 then 0 else 1 + Nat.log 10 z.natAbs

/-- The **relative precision** of a `SigFig`, i.e. how many digits are known.
For example `SigFig.prec 1e0 = 1`, `SigFig.prec 1.3 = 2`, and `SigFig.prec 0.000 = 0`. -/
abbrev prec (r : SigFig) : ℕ := prec_int r.m

@[simp]
theorem prec_def (r : SigFig) : r.prec = if r.m = 0 then 0 else 1 + Nat.log 10 r.m.natAbs :=
  rfl

/-- Round a sigfig to the nearest value with the given relative precision.
A naive implementation would be
```lean4
let δe := r.prec - p;
  ⟨round (r.m / 10 ^ δe : ℚ), r.e + δe⟩
```
but then `toPrec {m := 999, e := 0} 2` gives `{m := 100, e := 1}`, which itself has
a precision of 3. This isn't entirely unreasonable as a notion of rounding, but it
does mean that `(x.toPrec p).prec ≠ p`, which is a bit ridiculous. Accordingly, we
repeat this once more (which is sufficient to ensure convergence).
-/
def toPrec (r : SigFig) (p : ℕ) : SigFig :=
  let δe : ℤ := r.prec - p;
  let r' : SigFig :=
    ⟨round (r.m / 10 ^ δe : ℚ), r.e + δe⟩;
  let δ'e : ℤ := r'.prec - p;
    ⟨round (r'.m / 10 ^ δ'e : ℚ), r'.e + δ'e⟩

example : toPrec ⟨94, -1⟩ 1 = ⟨9, 0⟩ ∧ toPrec ⟨95, -1⟩ 1 = ⟨1, 1⟩ := by
  -- norm_num [toPrec] --TODO: NormNum extension for `round ℚ`?
  native_decide

@[simp]
theorem toPrec_self (r : SigFig) : r.toPrec r.prec = r := by
  ext <;> simp [toPrec]

--TODO
-- @[simp]
-- theorem toPrec_prec (r : SigFig) (p : ℕ) : (r.toPrec p).prec = p := by
--   sorry

--TODO
-- @[simp]
-- theorem toPrec_zero (r : SigFig) : (r.toPrec 0).m = 0 := by
--   sorry

/-- **Multiplication** is carried out by:
 * Multiplying the mantissas (as integers)
 * Adding the exponents
 * Rounding the lesser of the two relative precisions.
-/
def mul (r s : SigFig) : SigFig :=
  toPrec ⟨r.m * s.m, r.e + s.e⟩ (min r.prec s.prec)

instance : Mul SigFig :=
  ⟨mul⟩

theorem mul_def (r s : SigFig) : r * s = toPrec ⟨r.m * s.m, r.e + s.e⟩ (min r.prec s.prec) :=
  rfl

/-- Convert a real number to a `SigFig` at a given relative precision.
Note that `0` can never have any relative precision, so it defaults to just
`ofReal 0 p`, which has `p` digits of absolute precision but no well-defined
relative precision.

TODO: This might need some tweaking to get the rounding entirely optimal. -/
noncomputable def ofReal_prec (x : ℝ) (p : ℤ) : SigFig :=
  if x = 0 then ofReal 0 p
  else ⟨round (x * 10 ^ (p - Int.log 10 |x|) : ℝ), p - Int.log 10 |x|⟩

noncomputable instance : SMul ℝ SigFig where
  smul x r := r * ofReal_prec x r.prec

theorem hMul_real_def : x • r = r * ofReal_prec x r.prec := by
  rfl

theorem zero_smul : (0 : ℝ) • r = ⟨0, r.e + r.prec⟩ := by
  rcases r with ⟨m, e⟩
  simp [hMul_real_def, ofReal_prec, ofReal, mul_def, toPrec]

@[simp]
theorem zero_smul_m : ((0 : ℝ) • r).m = 0 := by
  simp [zero_smul]

@[simp]
theorem zero_smul_e : ((0 : ℝ) • r).e = r.e + r.prec := by
  simp [zero_smul]

proof_wanted one_smul : (1 : ℝ) • r = r

/-! We don't have `HasDistribNeg`, because:
```
-(3. * 1.5) =
-(toPrec 4.5 1) =
-5.
```
but
```
-3. * 1.5 =
toPrec (-4.5) 1 =
-4.
```
-/
example : -(mul ⟨3, 0⟩ ⟨15, -1⟩) = ⟨-5, 0⟩ ∧ mul (-⟨3, 0⟩) ⟨15, -1⟩ = ⟨-4, 0⟩ := by
  native_decide

end mul
