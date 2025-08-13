import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.RCLike.Basic

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

instance : SubtractionCommMonoid ℝRange :=
  inferInstance

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

@[simp]
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

/- # Multiplication -/

--See https://github.com/Timeroot/ComputableReal/blob/61221e0d67648119919bc51b27e693766f48c791/ComputableReal/ComputableRSeq.lean#L13C37-L23C1
/--Multiplication on intervals of ℚ. TODO: Should generalize to any LinearOrderedField... -/
def mul_pair (x y : ℝRange) : ℝRange :=
  let ⟨⟨xl,xu⟩,_⟩ := x
  let ⟨⟨yl,yu⟩,_⟩ := y
  ⟨⟨min (min (xl*yl) (xu*yl)) (min (xl*yu) (xu*yu)),
    max (max (xl*yl) (xu*yl)) (max (xl*yu) (xu*yu))⟩,
    by simp only [le_max_iff, min_le_iff, le_refl, true_or, or_true, or_self]⟩

instance : Mul ℝRange :=
  ⟨mul_pair⟩

theorem mul_fst (x y : ℝRange) : (x * y).fst =
    let ⟨⟨xl,xu⟩,_⟩ := x; let ⟨⟨yl,yu⟩,_⟩ := y; min (min (xl*yl) (xu*yl)) (min (xl*yu) (xu*yu)) := by
  rfl

theorem mul_snd (x y : ℝRange) : (x * y).snd =
    let ⟨⟨xl,xu⟩,_⟩ := x; let ⟨⟨yl,yu⟩,_⟩ := y; max (max (xl*yl) (xu*yl)) (max (xl*yu) (xu*yu)) := by
  rfl

set_option maxHeartbeats 500000 in
theorem ℝRange.mul_ext.extracted_1_2 (a b : ℝ) (h1 : a ≤ b) (c d : ℝ) (h2 : c ≤ d) :
  ∀ (c_1 : ℝ),
    ((a * c ≤ c_1 ∨ b * c ≤ c_1) ∨ a * d ≤ c_1 ∨ b * d ≤ c_1) ∧
        ((c_1 ≤ a * c ∨ c_1 ≤ b * c) ∨ c_1 ≤ a * d ∨ c_1 ≤ b * d) ↔
      ∃ a_1, (a ≤ a_1 ∧ a_1 ≤ b) ∧ ∃ b, (c ≤ b ∧ b ≤ d) ∧ c_1 = a_1 * b := by
  -- To prove the equivalence, we can use the fact that the product of two intervals is the interval spanned by the products of their endpoints.
  have h_prod : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, x * y ∈ Set.Icc (min (a * c) (min (a * d) (min (b * c) (b * d)))) (max (a * c) (max (a * d) (max (b * c) (b * d)))) := by
    aesop;
    -- Case 1
    · by_cases ha : a ≤ 0;
      -- Case 1
      · by_cases hb : b ≤ 0;
        -- Case 1
        · -- Since $a \leq x \leq b$ and $a, b \leq 0$, we have $x \leq 0$. Also, since $c \leq y \leq d$, we consider two cases: $y \geq 0$ and $y < 0$.
          by_cases hy_nonneg : 0 ≤ y;
          -- Case 1
          · exact Or.inr <| Or.inl <| by nlinarith;
          -- Case 2
          · exact Or.inr <| Or.inr <| Or.inr <| by nlinarith;
        -- Case 2
        · -- Since $a \leq 0$ and $b > 0$, we consider the sign of $x$ and $y$.
          by_cases hx : x ≤ 0;
          -- Case 1
          · by_cases hy : y ≤ 0;
            -- Case 1
            · contrapose! hb;
              nlinarith;
            -- Case 2
            · exact Or.inr <| Or.inl <| by nlinarith;
          -- Case 2
          · contrapose! hx;
            cases le_or_lt 0 y <;> nlinarith;
      -- Case 2
      · norm_num +zetaDelta at *;
        contrapose! ha;
        cases le_or_lt 0 x <;> cases le_or_lt 0 y <;> nlinarith;
    -- Case 2
    · -- Since $x \in [a, b]$ and $y \in [c, d]$, their product $x * y$ is bounded by the products of the endpoints.
      have h_bounds : x * y ≤ max (a * c) (max (a * d) (max (b * c) (b * d))) := by
        by_cases hx : 0 ≤ x;
        -- Case 1
        · field_simp;
          by_contra h_contra;
          push_neg at h_contra;
          cases le_or_lt 0 c <;> cases le_or_lt 0 d <;> nlinarith;
        -- Case 2
        · norm_num +zetaDelta at *;
          contrapose! hx;
          cases le_or_lt 0 c <;> cases le_or_lt 0 d <;> nlinarith;
      contrapose! h_bounds; aesop;
  -- To prove the reverse direction, assume $c_1$ is in the interval $[min(ac, ad, bc, bd), max(ac, ad, bc, bd)]$. We need to find $x \in [a, b]$ and $y \in [c, d]$ such that $c_1 = xy$.
  have h_reverse : ∀ c_1, min (a * c) (min (a * d) (min (b * c) (b * d))) ≤ c_1 ∧ c_1 ≤ max (a * c) (max (a * d) (max (b * c) (b * d))) → ∃ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc c d, c_1 = x * y := by
    -- By the intermediate value theorem, since the product function is continuous, the image of the rectangle [a, b] × [c, d] under the product function is connected. Therefore, it must contain all values between the minimum and maximum products.
    have h_connected : IsConnected (Set.image (fun p : ℝ × ℝ => p.1 * p.2) (Set.Icc a b ×ˢ Set.Icc c d)) := by
      apply_rules [ IsConnected.image, isConnected_Icc ];
      -- Case 1
      · exact ⟨ Set.Nonempty.prod ( Set.nonempty_Icc.2 h1 ) ( Set.nonempty_Icc.2 h2 ), isPreconnected_Icc.prod isPreconnected_Icc ⟩;
      -- Case 2
      · exact ContinuousOn.mul continuousOn_fst continuousOn_snd;
    have h_min : ∃ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc c d, x * y = min (a * c) (min (a * d) (min (b * c) (b * d))) := by
      cases min_cases ( a * c ) ( Min.min ( a * d ) ( Min.min ( b * c ) ( b * d ) ) ) <;> cases min_cases ( a * d ) ( Min.min ( b * c ) ( b * d ) ) <;> cases min_cases ( b * c ) ( b * d ) <;> first | exact ⟨ a, Set.left_mem_Icc.mpr h1, c, Set.left_mem_Icc.mpr h2, by linarith ⟩ | exact ⟨ a, Set.left_mem_Icc.mpr h1, d, Set.right_mem_Icc.mpr h2, by linarith ⟩ | exact ⟨ b, Set.right_mem_Icc.mpr h1, c, Set.left_mem_Icc.mpr h2, by linarith ⟩ | exact ⟨ b, Set.right_mem_Icc.mpr h1, d, Set.right_mem_Icc.mpr h2, by linarith ⟩ ;
    have h_max : ∃ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc c d, x * y = max (a * c) (max (a * d) (max (b * c) (b * d))) := by
      cases max_cases ( a * c ) ( Max.max ( a * d ) ( Max.max ( b * c ) ( b * d ) ) ) <;> cases max_cases ( a * d ) ( Max.max ( b * c ) ( b * d ) ) <;> cases max_cases ( b * c ) ( b * d ) <;> first | exact ⟨ a, ⟨ by linarith, by linarith ⟩, c, ⟨ by linarith, by linarith ⟩, by linarith ⟩ | exact ⟨ a, ⟨ by linarith, by linarith ⟩, d, ⟨ by linarith, by linarith ⟩, by linarith ⟩ | exact ⟨ b, ⟨ by linarith, by linarith ⟩, c, ⟨ by linarith, by linarith ⟩, by linarith ⟩ | exact ⟨ b, ⟨ by linarith, by linarith ⟩, d, ⟨ by linarith, by linarith ⟩, by linarith ⟩;
    intros c_1 hc_1;
    have := h_connected.Icc_subset ( Set.mem_image_of_mem _ <| Set.mk_mem_prod h_min.choose_spec.1 h_min.choose_spec.2.choose_spec.1 ) ( Set.mem_image_of_mem _ <| Set.mk_mem_prod h_max.choose_spec.1 h_max.choose_spec.2.choose_spec.1 );
    have := @this c_1;
    exact Exists.elim ( this ⟨ by linarith [ h_min.choose_spec.2.choose_spec.2 ], by linarith [ h_max.choose_spec.2.choose_spec.2 ] ⟩ ) fun x hx => ⟨ x.1, hx.1.1, x.2, hx.1.2, hx.2.symm ⟩;
  intro c_1;
  simp_all ( config := { decide := Bool.true } ) [ min_le_iff, le_max_iff ];
  apply Iff.intro;
  -- Case 1
  · exact fun h => h_reverse c_1 ( by tauto ) ( by tauto );
  -- Case 2
  · rintro ⟨ x, hx, y, hy, rfl ⟩ ; specialize h_prod x hx.1 hx.2 y hy.1 hy.2; aesop;

theorem mul_ext (x y : ℝRange) : ∀ c, c ∈ x * y ↔ ∃ a ∈ x, ∃ b ∈ y, c = a * b := by
  simp only [NonemptyInterval.mem_def, mul_fst, inf_le_iff, mul_snd, le_sup_iff]
  apply ℝRange.mul_ext.extracted_1_2 _ _ x.2 _ _ y.2

protected theorem mul_comm (x y : ℝRange) : x * y = y * x := by
  rcases x, y with ⟨⟨⟨a₁,a₂⟩, _⟩, ⟨⟨b₁,b₂⟩, _⟩⟩
  ext
  · simp [mul_fst, min_assoc, mul_comm b₁ _, mul_comm b₂ _]
    congr 1
    rw [← min_assoc, ← min_assoc, min_comm (_ * _)]
  · simp [mul_snd, max_assoc, mul_comm b₁ _, mul_comm b₂ _]
    congr 1
    rw [← max_assoc, ← max_assoc, max_comm (_ * _)]

protected theorem mul_assoc (x y z : ℝRange) : (x * y) * z = x * (y * z) := by
  simp [mul_ext, mem_ext_iff]
  intro _
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, ⟨c, hc, rfl⟩⟩
    exact ⟨a, ha, b * c, ⟨b, hb, c, hc, rfl⟩, mul_assoc a b c⟩
  · rintro ⟨a, ha, _, ⟨⟨b, hb, c, hc, rfl⟩, rfl⟩⟩
    exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, c, hc, (mul_assoc a b c).symm⟩

theorem pure_trichotomy (x : ℝRange) (y : ℝ) :
    x.snd < y ∨ y < x.fst ∨ y ∈ x := by
  rw [or_iff_not_imp_left, or_iff_not_imp_left]
  intro h₁ h₂
  push_neg at h₁ h₂
  exact ⟨h₂, h₁⟩

/-- The **inverse** of an interval. We take, as a junk value, that if 0 is in the interval,
then the inverse is the unique number 0. Otherwise, it's `[1/snd, 1/fst]` as one would expect. -/
instance : Inv ℝRange :=
  ⟨fun x ↦ open Classical in if h : 0 ∈ x then 0 else ⟨(x.snd⁻¹, x.fst⁻¹), by
    rcases pure_trichotomy x 0 with h₁ | h₂ | h_mem
    · have h₂ : x.fst < 0 := by linarith [x.2]
      simp [inv_le_inv_of_neg h₁ h₂, x.2]
    · have h₁ : 0 < x.snd := by linarith [x.2]
      simp [inv_le_inv₀ h₁ h₂, x.2]
    · contradiction
  ⟩⟩

theorem inv_of_zero_mem (x : ℝRange) (hx : 0 ∈ x) : x⁻¹ = 0 := by
  simp [instInv, hx]

theorem fst_inv_of_zero_notMem (x : ℝRange) (hx : 0 ∉ x) : (x⁻¹).fst = x.snd⁻¹ := by
  simp [instInv, hx]

theorem snd_inv_of_zero_notMem (x : ℝRange) (hx : 0 ∉ x) : (x⁻¹).snd = x.fst⁻¹ := by
  simp [instInv, hx]

instance : Div ℝRange :=
  ⟨fun x y ↦ x * y⁻¹⟩

theorem div_def (x y : ℝRange) : x / y = x * y⁻¹ := by
  rfl

instance : CommSemigroup ℝRange where
  mul_comm := ℝRange.mul_comm
  mul_assoc := ℝRange.mul_assoc

instance : MulZeroOneClass ℝRange where
  one_mul a := by
    ext <;> simp [mul_fst, mul_snd, a.2]
  mul_one a := by
    ext <;> simp [mul_fst, mul_snd, a.2]
  zero_mul a := by
    ext <;> simp [mul_fst, mul_snd]
  mul_zero a := by
    ext <;> simp [mul_fst, mul_snd]

/-
  At this point, we do have enough information to put a `Monoid` instance on ℝRange.
  We could even go so far as to give it `DivInvMonoid`. But, we don't do this. Why?
  Because then we get `NatPow` and `Pow ℝRange ℤ` instances immediately, that do NOT
  have the meaning we want. Powers of an interval are, generally speaking, not the
  same as repeated multiplication of an interval.

  As the simplest example: `[-2, 2] ^ 2` should be `[0, 4]`. But `[-2, 2] * [-2, 2]`
  evaluates to `[-4, 4]`, because the two "copies" of `[-2, 2]` could take different
  endpoints.

  We also don't have distributivity, so we couldn't be a Semiring. We also don't have
  additive group structure, and we don't have `InvolutiveInv`, because
  `([-1, 1]⁻¹)⁻¹ = 0⁻¹ = 0 ≠ [-1, 1]`.
-/

instance : InvOneClass ℝRange where
  inv_one := by
    ext <;> simp [fst_inv_of_zero_notMem, snd_inv_of_zero_notMem]

instance : CharZero ℝRange where
  cast_injective _ := by
    simp [NonemptyInterval.ext_iff]

-- TODO
instance : IsCancelMulZero ℝRange where
  mul_left_cancel_of_ne_zero := sorry
  mul_right_cancel_of_ne_zero := sorry

instance : HasDistribNeg ℝRange where
  neg_mul := sorry
  mul_neg := sorry


/- Normally the theorem `div_eq_mul_inv` is great, but here we need a special version because
we're not a `DivInvMonoid`, for the reasons above. -/
protected theorem div_eq_mul_inv (x y : ℝRange) : x / y = x * y⁻¹ := by
  rfl

--TODO: Copies of `inv_eq_of_mul`, `mul_inv_rev`,
-- `inv_eq_of_mul_eq_one_left`, `eq_inv_of_mul_eq_one_left`

def natPow (x : ℝRange) (n : ℕ) : ℝRange :=
  if h : Even n then
    let lb := min (abs x.fst) (abs x.snd);
    let ub := max (abs x.fst) (abs x.snd);
    ⟨(lb ^ n, ub ^ n), sorry⟩
  else
    ⟨⟨x.fst ^ n, x.snd ^ n⟩, sorry⟩

instance : NatPow ℝRange :=
  ⟨natPow⟩

@[simp]
theorem natPow_even_fst (x : ℝRange) {n : ℕ} (hn : Even n) :
    (x ^ n).fst = (min (abs x.fst) (abs x.snd)) ^ n :=
  congrArg Prod.fst <| congrArg NonemptyInterval.toProd (dif_pos hn)

@[simp]
theorem natPow_even_snd (x : ℝRange) {n : ℕ} (hn : Even n) :
    (x ^ n).snd = (max (abs x.fst) (abs x.snd)) ^ n :=
  congrArg Prod.snd <| congrArg NonemptyInterval.toProd (dif_pos hn)

@[simp]
theorem natPow_odd_fst (x : ℝRange) {n : ℕ} (hn : Odd n) :
    (x ^ n).fst = (x.fst) ^ n :=
  congrArg Prod.fst <| congrArg NonemptyInterval.toProd (dif_neg (Nat.not_even_iff_odd.mpr hn))

@[simp]
theorem natPow_odd_snd (x : ℝRange) {n : ℕ} (hn : Odd n) :
    (x ^ n).snd = (x.snd) ^ n :=
  congrArg Prod.snd <| congrArg NonemptyInterval.toProd (dif_neg (Nat.not_even_iff_odd.mpr hn))

@[simp]
protected theorem pow_zero (x : ℝRange) : x ^ 0 = 1 := by
  ext <;> simp

@[simp]
protected theorem pow_one (x : ℝRange) : x ^ 1 = x := by
  ext <;> simp

--Note that `pow_add` doesn't hold unless (1) both numbers are even, or (2) the interval
-- is nonnegative.

--TODO: Mathlibbable...?
theorem min_natpow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    min x y ^ n = min (x ^ n) (y ^ n) := by
  sorry

theorem max_natpow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    max x y ^ n = max (x ^ n) (y ^ n) := by
  sorry

protected theorem pow_mul (x : ℝRange) (a b : ℕ) : (x ^ a) ^ b = x ^ (a * b) := by
  rcases Nat.even_or_odd a with ha | ha
  · rcases Nat.even_or_odd b with hb | hb
    · have h₁ : abs (min |x.toProd.1| |x.toProd.2|) = min |x.toProd.1| |x.toProd.2| := by
        simp
      have h₂ : abs (max |x.toProd.1| |x.toProd.2|) = max |x.toProd.1| |x.toProd.2| := by
        simp
      ext
      · simp only [hb, natPow_even_fst, natPow_even_snd, ha, Even.mul_left, pow_mul, abs_pow]
        rw [← min_natpow (by positivity) (by positivity)]
        simp [h₁, h₂]
      · simp only [hb, natPow_even_fst, natPow_even_snd, ha, Even.mul_left, pow_mul, abs_pow]
        rw [← max_natpow (by positivity) (by positivity)]
        simp [h₁, h₂]
    · ext <;> simp [ha, hb, pow_mul]
  · rcases Nat.even_or_odd b with hb | hb
    · ext
      · simp [ha, hb, pow_mul]
        rw [← min_natpow (by positivity) (by positivity)]
      · simp [ha, hb, pow_mul]
        rw [← max_natpow (by positivity) (by positivity)]
    · ext <;> simp [ha, hb, pow_mul]

/- # Simplifying pure expressions -/

--Don't want to mark `ℝRange.pure` as a `coe` because then we lose some of the control over
--delaboration that we want to keep. So, we can't do `attribute [coe] pure`. But,
--`norm_cast` doesn't accept adding lemmas that don'e have a `coe`-function, either.
--So, we need to manually add them to the simpExtension: see the #eval's below.

@[simp]
theorem pure_add_pure (x y : ℝ) : pure (x + y) = x + y :=
  NonemptyInterval.pure_add_pure x y

@[simp]
theorem neg_pure (x : ℝ) : pure (-x) = -x :=
  NonemptyInterval.neg_pure x

@[simp]
theorem pure_sub_pure (x y : ℝ) : pure (x - y) = x - y :=
  NonemptyInterval.pure_sub_pure x y

@[simp]
theorem pure_natCast (n : ℕ) : pure (n : ℝ) = n := by
  rfl

@[simp]
theorem pure_intCast (z : ℤ) : pure (z : ℝ) = z := by
  rfl

@[simp]
theorem pure_ratCast (q : ℚ) : pure (q : ℝ) = q := by
  rfl

@[simp]
theorem pure_mul_pure (x y : ℝ) : pure (x * y) = x * y := by
  ext
  · simp [mul_fst]
  · simp [mul_snd]

@[simp]
theorem inv_pure (x : ℝ) : x⁻¹ = (pure x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, inv_of_zero_mem]
  ext
  · simp [fst_inv_of_zero_notMem, Ne.symm hx]
  · simp [snd_inv_of_zero_notMem, Ne.symm hx]

@[simp]
theorem pure_div_pure (x y : ℝ) : pure (x / y) = x / y := by
  rw [ℝRange.div_eq_mul_inv, div_eq_mul_inv, pure_mul_pure]
  rw [← inv_pure]

#eval Lean.Meta.NormCast.addMove `ℝRange.pure_add_pure
#eval Lean.Meta.NormCast.addMove `ℝRange.neg_pure
#eval Lean.Meta.NormCast.addMove `ℝRange.pure_sub_pure
#eval Lean.Meta.NormCast.addSquash `ℝRange.pure_natCast
#eval Lean.Meta.NormCast.addSquash `ℝRange.pure_ratCast
#eval Lean.Meta.NormCast.addMove `ℝRange.pure_mul_pure
#eval Lean.Meta.NormCast.addMove `ℝRange.inv_pure
#eval Lean.Meta.NormCast.addMove `ℝRange.pure_div_pure

/-- Similar to `Rat.cast_add`, but that doesn't work here since we're not in a `Ring`. -/
@[simp, norm_cast]
theorem ratCast_add (x y : ℚ) : ((x + y : ℚ) : ℝRange) = x + y := by
  simp only [← pure_ratCast, pure_add_pure, Rat.cast_add]

/-- Similar to `Rat.cast_neg`, but that doesn't work here since we're not in a `Ring`. -/
@[simp, norm_cast]
theorem ratCast_neg (x : ℚ) : ((-x : ℚ) : ℝRange) = -x := by
  simp only [← pure_ratCast, neg_pure, Rat.cast_neg]

/-- Similar to `Rat.cast_sub`, but that doesn't work here since we're not in a `Ring`. -/
@[simp, norm_cast]
theorem ratCast_sub (x y : ℚ) : ((x - y : ℚ) : ℝRange) = x - y := by
  simp only [← pure_ratCast, pure_sub_pure, Rat.cast_sub]

/-- Similar to `Rat.cast_mul`, but that doesn't work here since we're not in a `Ring`. -/
@[simp, norm_cast]
theorem ratCast_mul (x y : ℚ) : ((x * y : ℚ) : ℝRange) = x * y := by
  simp only [← pure_ratCast, pure_mul_pure, Rat.cast_mul]

/-- Similar to `Rat.cast_inv`, but that doesn't work here since we're not in a `Ring`. -/
@[simp, norm_cast]
theorem ratCast_inv (x : ℚ) : x⁻¹ = ((x : ℚ) : ℝRange)⁻¹ := by
  simp only [← pure_ratCast, inv_pure, Rat.cast_inv]

/-- Similar to `Rat.cast_div`, but that doesn't work here since we're not in a `Ring`. -/
@[simp, norm_cast]
theorem ratCast_div (x y : ℚ) : ((x / y : ℚ) : ℝRange) = x / y := by
  simp [div_def, div_eq_mul_inv]

/-- Similar to `Rat.cast_natCast`, but that doesn't work here since we're not in a `Ring`.-/
@[simp, norm_cast]
theorem ratCast_natCast (n : ℕ) : ((n : ℚ) : ℝRange) = n := by
  ext <;> simp

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
