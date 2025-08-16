import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.RCLike.Basic

import SigFigs.ForMathlib

/-- A `ℝRange` for a range of possible real values associated to a quantity with uncertainty. It's
a `NonemptyInterval ℝ`, but we give it some other useful instances. -/
abbrev ℝRange := NonemptyInterval ℝ

noncomputable section
namespace ℝRange

abbrev pure : ℝ → ℝRange := NonemptyInterval.pure

instance : Coe ℝ ℝRange := ⟨pure⟩

/- # Additive structure and casting -/
instance : AddCommMonoidWithOne ℝRange where
  natCast_zero := by
    ext <;> change ((0 : ℕ) : ℝ) = 0 <;> simp
  natCast_succ n := by
    ext <;> change ((n + 1 : ℕ) : ℝ) = n + 1 <;> simp

instance : IntCast ℝRange :=
  ⟨(pure ·)⟩

instance : RatCast ℝRange :=
  ⟨(pure ·)⟩

instance : Membership ℝ ℝRange :=
  inferInstance

@[simp]
theorem fst_mem (x : ℝRange) : x.fst ∈ x := by
  simp [NonemptyInterval.mem_def, x.2]

@[simp]
theorem snd_mem (x : ℝRange) : x.snd ∈ x := by
  simp [NonemptyInterval.mem_def, x.2]

theorem mem_ext_iff (x y : ℝRange) : x = y ↔ ∀ a, a ∈ x ↔ a ∈ y := by
  use (by simp [·])
  intro h
  have h₁ := And.intro (h x.fst) (h x.snd)
  have h₂ := And.intro (h y.fst) (h y.snd)
  simp [↓fst_mem, ↓snd_mem, NonemptyInterval.mem_def] at h₁ h₂
  rcases h₁, h₂ with ⟨⟨⟨_,_⟩,⟨_,_⟩⟩,⟨_,_⟩,_,_⟩
  ext <;> order

@[simp]
theorem toProd_ofNat (n : ℕ) [n.AtLeastTwo] :
    (NonemptyInterval.toProd (ofNat(n) : ℝRange)) = (ofNat(n), ofNat(n)) := by
  rfl

@[simp]
theorem toProd_natCast (n : ℕ) :
    (NonemptyInterval.toProd (n : ℝRange)) = ((n : ℝ), (n : ℝ)) := by
  rfl

@[simp]
theorem toProd_intCast (z : ℤ) :
    (NonemptyInterval.toProd (z : ℝRange)) = ((z : ℝ), (z : ℝ)) := by
  rfl

@[simp]
theorem toProd_ratCast (q : ℚ) :
    (NonemptyInterval.toProd (q : ℝRange)) = ((q : ℝ), (q : ℝ)) := by
  rfl

@[simp↓] --mark as ↓ so that, in `(pure (x + y)).toProd`, we do the toProd first.
theorem toProd_pure (x : ℝ) :
    (NonemptyInterval.toProd (pure x : ℝRange)) = (x, x) := by
  rfl

@[simp]
theorem mem_zero (x : ℝ) : x ∈ (0 : ℝRange) ↔ x = 0 := by
  rw [← NonemptyInterval.pure_zero, NonemptyInterval.mem_pure]

@[simp]
theorem mem_one (x : ℝ) : x ∈ (1 : ℝRange) ↔ x = 1 := by
  rw [← NonemptyInterval.pure_one, NonemptyInterval.mem_pure]

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

/- # Simplifying pure expressions -/

--`pure_zero`, `pure_one`, `pure_natCast`, `pure_add_pure` are already simp'ed in `NonemptyInterval`.

theorem pure_zero : (pure (0 : ℝ)) = (0 : ℝRange) := by
  simp says simp only [NonemptyInterval.pure_zero]

theorem pure_one : (pure (1 : ℝ)) = (1 : ℝRange) := by
  simp says simp only [NonemptyInterval.pure_one]

theorem pure_natCast (n : ℕ) : pure (n : ℝ) = n := by
  simp says simp only [NonemptyInterval.pure_natCast]

theorem pure_add_pure (x y : ℝ) : pure (x + y) = x + y := by
  simp says simp only [NonemptyInterval.pure_add_pure]

@[simp]
theorem pure_ofNat (n : ℕ) [n.AtLeastTwo] :
    (pure (ofNat(n) : ℝ)) = (ofNat(n) : ℝRange) := by
  rfl

theorem pure_injective : pure.Injective := by
  intro _ _ h
  rw [NonemptyInterval.ext_iff, Prod.ext_iff] at h
  exact h.1

@[simp]
theorem pure_eq_pure (x y : ℝ) : pure x = pure y ↔ x = y := by
  use @pure_injective _ _
  rintro rfl
  rfl

@[simp]
theorem pure_intCast (z : ℤ) : pure (z : ℝ) = z := by
  rfl

@[simp]
theorem pure_ratCast (q : ℚ) : pure (q : ℝ) = q := by
  rfl

/-
Note: We don't want to mark `ℝRange.pure` as a `coe` because then we lose some of the control over
  delaboration that we want to keep. So, we can't do `attribute [coe] pure`. But,
  `norm_cast` doesn't accept adding lemmas that don'e have a `coe`-function, either.
  So, we need to manually add them to the simpExtension: see the #eval's below.
-/
#eval Lean.Meta.NormCast.addElim `ℝRange.pure_ofNat
#eval Lean.Meta.NormCast.addElim `ℝRange.pure_eq_pure
#eval Lean.Meta.NormCast.addMove `ℝRange.pure_add_pure
#eval Lean.Meta.NormCast.addSquash `ℝRange.pure_natCast
#eval Lean.Meta.NormCast.addSquash `ℝRange.pure_intCast
#eval Lean.Meta.NormCast.addSquash `ℝRange.pure_ratCast

--This example has four different coercions: `pure`, `Real.instNatCast`, `ℝRange.instRatCast`,
-- and `Rat.instNatCast`. This is a sort of sanity check that we're linking these all
-- together correctly
example (x y : ℕ) : pure (x + y) = ((x + y : ℚ) : ℝRange) := by
  norm_cast

example (x : ℝ) (hx : x = 3) : pure (3 + 5) = x + pure 5 := by
  rw [hx]
  norm_cast

example (x : ℝ) (hx : x = 3 / 5) : pure ((3 / 5 : ℚ) + 5) = x + pure 5 := by
  simp only [Rat.cast_div, Rat.cast_ofNat, hx]
  norm_cast

/-- **Lifting* a function** from the reals to intervals. For a monotone function, this just maps the
endpoints; but in general we need to consider the min/max within the interval.

If the function isn't bounded on this interval, then we give the junk value `[0, 0]`. This is relatively
rare - it can't happen if the function is continuous - so we would like to cordon off this ugly
behavior where possible. Thus, this is marked irreducible.
-/
@[irreducible]
noncomputable def map (f : ℝ → ℝ) (x : ℝRange) : ℝRange :=
  open Classical in
  if h : BddBelow (f '' x) ∧ BddAbove (f '' x) then
    ⟨⟨sInf (f '' x), sSup (f '' x)⟩,
      csInf_le_csSup h.1 h.2 ((NonemptyInterval.coe_nonempty x).image f)⟩
  else 0

theorem map_def_of_bddBelow_bddAbove {f : ℝ → ℝ} {x : ℝRange} (h₁ : BddBelow (f '' x)) (h₂ : BddAbove (f '' x)) :
    map f x = ⟨⟨sInf (f '' x), sSup (f '' x)⟩,
      csInf_le_csSup h₁ h₂ ((NonemptyInterval.coe_nonempty x).image f)⟩ := by
  unfold map
  exact dif_pos ⟨h₁, h₂⟩

theorem map_def_of_isBounded {f : ℝ → ℝ} {x : ℝRange} (h : Bornology.IsBounded (f '' x)) :
    map f x = ⟨⟨sInf (f '' x), sSup (f '' x)⟩,
      csInf_le_csSup (isBounded_iff_bddBelow_bddAbove.mp h).1 (isBounded_iff_bddBelow_bddAbove.mp h).2
        ((NonemptyInterval.coe_nonempty x).image f)⟩ := by
  rw [isBounded_iff_bddBelow_bddAbove] at h
  exact map_def_of_bddBelow_bddAbove h.1 h.2

theorem map_def_of_not_isBounded {f : ℝ → ℝ} {x : ℝRange} (h : ¬Bornology.IsBounded (f '' x)) :
    map f x = 0 := by
  rw [isBounded_iff_bddBelow_bddAbove] at h
  unfold map
  exact dif_neg h

/- `ℝRange.map` is a valid bound on the image, when the image is bounded. -/
theorem image_subset_map_of_isBounded {f : ℝ → ℝ} {x : ℝRange} (h : Bornology.IsBounded (f '' x)) :
    f '' x ⊆ (map f x : Set ℝ) := by
  intro y hy
  simp only [Set.mem_image, SetLike.mem_coe, NonemptyInterval.mem_def, map_def_of_isBounded h] at hy ⊢
  rw [isBounded_iff_bddBelow_bddAbove] at h
  exact ⟨csInf_le h.1 hy, le_csSup h.2 hy⟩

section nicemaps
/- For a few different classes of 'nice' maps, the image is well-behaved. These include continuous,
monotone, and antitone functions. These also all occur as typeclasses: `ContinuousMapClass`,
`OrderHomClass`, and `OrderHomClass _ _ᵒᵈ`. We can also include `OrderIso` as a continuous map
but really it should just be equipped with a `ContinuousMapClass` instances itself. (It already
has `OrderHomClass` of course.) See #28416 in ForMathlib.lean
-/

variable {F : Type*} [FunLike F ℝ ℝ]

theorem map_continuousOn (x : ℝRange) {f : ℝ → ℝ} (hf : ContinuousOn f x) :
    map f x = ⟨⟨sInf (f '' (x : Set ℝ)), sSup (f '' (x : Set ℝ))⟩,
      csInf_le_csSup
        (CompactIccSpace.isCompact_Icc.bddBelow_image hf)
        (CompactIccSpace.isCompact_Icc.bddAbove_image hf)
        ((NonemptyInterval.coe_nonempty x).image f)⟩ := by
  unfold map
  rw [dif_pos]
  use CompactIccSpace.isCompact_Icc.bddBelow_image hf
  exact CompactIccSpace.isCompact_Icc.bddAbove_image hf

theorem map_continuous {f : ℝ → ℝ} (hf : Continuous f) (x : ℝRange) :
  map f x = ⟨⟨sInf (f '' (x : Set ℝ)), sSup (f '' (x : Set ℝ))⟩,
    csInf_le_csSup
      (CompactIccSpace.isCompact_Icc.bddBelow_image hf.continuousOn)
      (CompactIccSpace.isCompact_Icc.bddAbove_image hf.continuousOn)
      ((NonemptyInterval.coe_nonempty x).image f)⟩ :=
  map_continuousOn x hf.continuousOn

@[simp]
theorem map_continuousMapClass [ContinuousMapClass F ℝ ℝ] (f : F) (x : ℝRange) :
  map f x = ⟨⟨sInf (f '' (x : Set ℝ)), sSup (f '' (x : Set ℝ))⟩,
    csInf_le_csSup
      (CompactIccSpace.isCompact_Icc.bddBelow_image (ContinuousMapClass.map_continuous f).continuousOn)
      (CompactIccSpace.isCompact_Icc.bddAbove_image (ContinuousMapClass.map_continuous f).continuousOn)
      ((NonemptyInterval.coe_nonempty x).image f)⟩ :=
  map_continuousOn x (ContinuousMapClass.map_continuous f).continuousOn

@[simp]
theorem map_continuousOn_eq_image {x : ℝRange} {f : ℝ → ℝ} (hf : ContinuousOn f x) :
    ↑(map f x) = f '' x := by
  rw [map_continuousOn x hf, eq_comm]
  simp only [NonemptyInterval.setLike]
  apply eq_Icc_of_connected_compact
  · exact (isConnected_Icc x.2).image f hf
  · exact CompactIccSpace.isCompact_Icc.image_of_continuousOn hf

@[simp]
theorem map_continuous_eq_image {f : ℝ → ℝ} (hf : Continuous f) (x : ℝRange) :
    ↑(map f x) = f '' x :=
  map_continuousOn_eq_image hf.continuousOn

@[simp]
theorem map_continuousMapClass_eq_image [ContinuousMapClass F ℝ ℝ] (f : F)  (x : ℝRange) :
    ↑(map f x) = f '' x :=
  map_continuous_eq_image (ContinuousMapClass.map_continuous f) x

theorem map_monotoneOn (x : ℝRange) {f : ℝ → ℝ} (hf : MonotoneOn f x) :
    map f x = ⟨⟨f x.fst, f x.snd⟩, hf (by simp) (by simp) x.2⟩ := by
  have hb : BddBelow (f '' x) := by
    apply hf.map_bddBelow .rfl
    use x.fst
    simp [NonemptyInterval.mem_def, lowerBounds, x.2]
    tauto
  have ha : BddAbove (f '' x) := by
    apply hf.map_bddAbove .rfl
    use x.snd
    simp [NonemptyInterval.mem_def, upperBounds, x.2]
  rw [map, dif_pos ⟨hb, ha⟩, NonemptyInterval.mk.injEq, Prod.mk.injEq]
  constructor
  · convert hf.sInf_image_Icc x.2
  · convert hf.sSup_image_Icc x.2

@[simp]
theorem map_monotone {f : ℝ → ℝ} (hf : Monotone f) (x : ℝRange) :
    map f x = ⟨⟨f x.fst, f x.snd⟩, hf x.2⟩ :=
  map_monotoneOn x (hf.monotoneOn _)

@[simp]
theorem map_orderHomClass [OrderHomClass F ℝ ℝ] (f : F) (x : ℝRange) :
    map f x = ⟨⟨f x.fst, f x.snd⟩, OrderHomClass.mono f x.2⟩ :=
  map_monotone (OrderHomClass.mono f) x

theorem map_antitoneOn (x : ℝRange) {f : ℝ → ℝ} (hf : AntitoneOn f x) :
    map f x = ⟨⟨f x.snd, f x.fst⟩, hf (by simp) (by simp) x.2⟩ := by
  have ha : BddAbove (f '' x) := by
    apply hf.map_bddBelow .rfl
    use x.fst
    simp [NonemptyInterval.mem_def, lowerBounds, x.2]
    tauto
  have hb : BddBelow (f '' x) := by
    apply hf.map_bddAbove .rfl
    use x.snd
    simp [NonemptyInterval.mem_def, upperBounds, x.2]
  rw [map, dif_pos ⟨hb, ha⟩, NonemptyInterval.mk.injEq, Prod.mk.injEq]
  constructor
  · convert hf.sInf_image_Icc x.2
  · convert hf.sSup_image_Icc x.2

@[simp]
theorem map_antitone {f : ℝ → ℝ} (hf : Antitone f) (x : ℝRange) :
    map f x = ⟨⟨f x.snd, f x.fst⟩, hf x.2⟩ :=
  map_antitoneOn x (hf.antitoneOn _)

@[simp]
theorem map_orderHomClass_orderDual [OrderHomClass F ℝ ℝᵒᵈ] (f : F) (x : ℝRange) :
    map f x = ⟨⟨f x.snd, f x.fst⟩, OrderHomClass.mono (β := ℝᵒᵈ) f x.2⟩ :=
  map_antitone (OrderHomClass.mono (β := ℝᵒᵈ) f) x

end nicemaps

@[simp]
theorem map_pure (f : ℝ → ℝ) (x : ℝ) : map f (pure x) = f x := by
  ext <;> simp [map]

scoped instance : FunLike (ℝ → ℝ) ℝRange ℝRange where
  coe f := ℝRange.map f
  coe_injective' _ _ h := by
    funext x
    simpa using congrFun h x

/-- This simp lemma, arguably, makes things slightly harder to read: a simple coercion
is turned into a `map f`. But frequently enough, I expect, the implicitness of this
could confuse the reader, and make copying claims (e.g. for a `have`) harder. In this
case, it seems better to encourage explicitness of the cast. -/
@[simp]
theorem funLike_eq_map (f : ℝ → ℝ) : (⇑f : ℝRange → ℝRange) = map f := by
  rfl

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

end ℝRange
