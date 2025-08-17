import SigFigs.Interval.Basic

/-! # Field operations on ℝRange intervals

This file defines the various field operations on `ℝRange`. We provide the simp lemmas
connecting these to `NatCast`, `IntCast`, `RatCast`, `ℝRange.pure`, and `ℝRange.map`
as appropriate.

Only zero, one, and addition are already defined at this point (in Interval/Basic.lean),
because those are needed to get the `NatCast` instance from `AddCommMonoid`.
-/

noncomputable section
namespace ℝRange

/- # Negation, Subtraction, Multiplication, Inverse, Division -/

instance : SubtractionCommMonoid ℝRange :=
  inferInstance

--TODO: AddCancelMonoid? Even better?

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

private theorem mul_ext_bash {a b c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) :
  ∀ (c_1 : ℝ),
    ((a * c ≤ c_1 ∨ b * c ≤ c_1) ∨ a * d ≤ c_1 ∨ b * d ≤ c_1) ∧
        ((c_1 ≤ a * c ∨ c_1 ≤ b * c) ∨ c_1 ≤ a * d ∨ c_1 ≤ b * d) ↔
      ∃ a_1, (a ≤ a_1 ∧ a_1 ≤ b) ∧ ∃ b, (c ≤ b ∧ b ≤ d) ∧ c_1 = a_1 * b := by
  -- To prove the equivalence, we can use the fact that the product of two intervals is the interval spanned by the products of their endpoints.
  have h_prod : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, x * y ∈ Set.Icc
      (min (a * c) (min (a * d) (min (b * c) (b * d)))) (max (a * c) (max (a * d) (max (b * c) (b * d)))) := by
    rintro x ⟨hax, hxb⟩ y ⟨hcy, hyd⟩
    simp only [Set.mem_Icc, inf_le_iff, le_sup_iff]
    constructor
    · by_cases hb : b ≤ 0
      · by_cases hy_nonneg : 0 ≤ y
        · exact .inr <| .inl <| by nlinarith
        · exact .inr <| .inr <| .inr <| by nlinarith
      by_cases hy : y ≤ 0
      · exact .inr <| .inr <| .inl <| by nlinarith
      by_cases ha : a ≤ 0
      · exact .inr <| .inl <| by nlinarith
      · exact .inl <| by nlinarith
    · -- Since $x \in [a, b]$ and $y \in [c, d]$, their product $x * y$ is bounded by the products of the endpoints.
      by_cases hx : 0 ≤ x
      · by_cases hd : d ≤ 0
        · exact .inr <| .inl <| by nlinarith
        · exact .inr <| .inr <| .inr <| by nlinarith
      by_cases hd : d ≤ 0 ∨ c ≤ 0
      · cases hd <;> exact .inl <| by nlinarith
      push_neg at hd
      exact .inr <| .inr <| .inl <| by nlinarith
  -- To prove the reverse direction, assume $v$ is in the interval $[min(ac, ad, bc, bd), max(ac, ad, bc, bd)]$. We need to find $x \in [a, b]$ and $y \in [c, d]$ such that $v = xy$.
  have h_reverse : ∀ v,
        min (a * c) (min (a * d) (min (b * c) (b * d))) ≤ v ∧
        v ≤ max (a * c) (max (a * d) (max (b * c) (b * d))) →
      ∃ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc c d, v = x * y := by
    -- By the intermediate value theorem, since the product function is continuous, the image of the rectangle [a, b] × [c, d] under the product function is connected. Therefore, it must contain all values between the minimum and maximum products.
    have h_connected : IsConnected ((fun p ↦ p.1 * p.2) '' Set.Icc a b ×ˢ Set.Icc c d) := by
      apply_rules [IsConnected.image, isConnected_Icc, IsConnected.prod]
      exact continuousOn_fst.mul continuousOn_snd
    have ⟨x_min, hx_min, y_min, hy_min, hxy_min⟩ : ∃ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc c d,
        x * y = min (a * c) (min (a * d) (min (b * c) (b * d))) := by
      cases min_cases (a * c) (min (a * d) (min (b * c) (b * d)))
      · exact ⟨a, ⟨le_rfl, h1⟩, c, ⟨le_rfl, h2⟩, by linarith⟩
      cases min_cases (a * d) (min (b * c) (b * d))
      · exact ⟨a, ⟨le_rfl, h1⟩, d, ⟨h2, le_rfl⟩, by linarith⟩
      cases min_cases (b * c) (b * d)
      · exact ⟨b, ⟨h1, le_rfl⟩, c, ⟨le_rfl, h2⟩, by linarith⟩
      · exact ⟨b, ⟨h1, le_rfl⟩, d, ⟨h2, le_rfl⟩, by linarith⟩
    have ⟨x_max, hx_max, y_max, hy_max, hxy_max⟩ : ∃ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc c d,
        x * y = max (a * c) (max (a * d) (max (b * c) (b * d))) := by
      cases max_cases (a * c) (max (a * d) (max (b * c) (b * d)))
      · exact ⟨a, ⟨le_rfl, h1⟩, c, ⟨le_rfl, h2⟩, by linarith⟩
      cases max_cases (a * d) (max (b * c) (b * d))
      · exact ⟨a, ⟨le_rfl, h1⟩, d, ⟨h2, le_rfl⟩, by linarith⟩
      cases max_cases (b * c) (b * d)
      · exact ⟨b, ⟨h1, le_rfl⟩, c, ⟨le_rfl, h2⟩, by linarith⟩
      · exact ⟨b, ⟨h1, le_rfl⟩, d, ⟨h2, le_rfl⟩, by linarith⟩
    have h_sub := h_connected.Icc_subset
      (Set.mem_image_of_mem _ <| Set.mk_mem_prod hx_min hy_min)
      (Set.mem_image_of_mem _ <| Set.mk_mem_prod hx_max hy_max)
    intros v hv
    obtain ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, rfl⟩⟩ := h_sub ⟨hxy_min ▸ hv.1, hxy_max ▸ hv.2⟩
    exact ⟨x, hx, y, hy, rfl⟩
  simp only [Set.mem_Icc, inf_le_iff, le_sup_iff, and_imp] at h_prod h_reverse
  refine fun c ↦ ⟨fun _ ↦ h_reverse c (by tauto) (by tauto), ?_⟩
  rintro ⟨x, hx, y, hy, rfl⟩
  specialize h_prod x hx.1 hx.2 y hy.1 hy.2
  tauto

theorem mul_ext (x y : ℝRange) : ∀ c, c ∈ x * y ↔ ∃ a ∈ x, ∃ b ∈ y, c = a * b := by
  simp only [NonemptyInterval.mem_def, mul_fst, inf_le_iff, mul_snd, le_sup_iff]
  apply ℝRange.mul_ext_bash x.2 y.2

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

theorem mem_trichotomy (x : ℝRange) (y : ℝ) :
    x.snd < y ∨ y < x.fst ∨ y ∈ x := by
  rw [or_iff_not_imp_left, or_iff_not_imp_left]
  intro h₁ h₂
  push_neg at h₁ h₂
  exact ⟨h₂, h₁⟩

/-- The **inverse** of an interval. We take, as a junk value, that if 0 is in the interval,
then the inverse is the unique number 0. Otherwise, it's `[1/snd, 1/fst]` as one would expect. -/
instance : Inv ℝRange :=
  ⟨fun x ↦ open Classical in if h : 0 ∈ x then 0 else ⟨(x.snd⁻¹, x.fst⁻¹), by
    rcases mem_trichotomy x 0 with h₁ | h₂ | h_mem
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

/-! # Casting lemmas -/

@[simp]
theorem neg_pure (x : ℝ) : pure (-x) = -x :=
  NonemptyInterval.neg_pure x

@[simp]
theorem pure_sub_pure (x y : ℝ) : pure (x - y) = x - y :=
  NonemptyInterval.pure_sub_pure x y

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

noncomputable instance : MinimalRing ℝRange where

/-- `ℝRange.pure` bundled as a `01+*` homomorphism. -/
@[simps apply]
def pureHom : MinimalRingHom ℝ ℝRange where
  toFun := pure
  map_zero' := rfl
  map_one' := rfl
  map_add' := by simp
  map_mul' := by simp

/-! # Natural and integer powers -/

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

/-- `natPow` coincides with the canonically lifted `map`. -/
@[simp]
theorem map_natPow (n : ℕ) : map (· ^ n) = (· ^ n) := by
  sorry

@[simp]
theorem coe_natPow (n : ℕ) : (⇑(· ^ n : ℝ → ℝ)) = (· ^ n) := by
  simp

--TODO appropriate `mem` lemmas

@[simp]
protected theorem pow_zero (x : ℝRange) : x ^ 0 = 1 := by
  ext <;> simp

@[simp]
protected theorem pow_one (x : ℝRange) : x ^ 1 = x := by
  ext <;> simp

--We prove `pow_mul`, but note that `pow_add` doesn't hold unless (1) both numbers are even,
--or (2) the interval is entirely nonnegative.

protected theorem pow_mul (x : ℝRange) (a b : ℕ) : (x ^ a) ^ b = x ^ (a * b) := by
  rcases Nat.even_or_odd a with ha | ha
  · rcases Nat.even_or_odd b with hb | hb
    · have h₁ : abs (min |x.toProd.1| |x.toProd.2|) = min |x.toProd.1| |x.toProd.2| := by
        simp
      have h₂ : abs (max |x.toProd.1| |x.toProd.2|) = max |x.toProd.1| |x.toProd.2| := by
        simp
      ext
      · simp only [hb, natPow_even_fst, natPow_even_snd, ha, Even.mul_left, pow_mul, abs_pow]
        rw [← Real.min_natPow (by positivity) (by positivity)]
        simp [h₁, h₂]
      · simp only [hb, natPow_even_fst, natPow_even_snd, ha, Even.mul_left, pow_mul, abs_pow]
        rw [← Real.max_natPow (by positivity) (by positivity)]
        simp [h₁, h₂]
    · ext <;> simp [ha, hb, pow_mul]
  · rcases Nat.even_or_odd b with hb | hb
    · ext
      · simp [ha, hb, pow_mul]
        rw [← Real.min_natPow (by positivity) (by positivity)]
      · simp [ha, hb, pow_mul]
        rw [← Real.max_natPow (by positivity) (by positivity)]
    · ext <;> simp [ha, hb, pow_mul]

--TODO IntPow

/-
Note: We don't want to mark `ℝRange.pure` as a `coe` because then we lose some of the control over
  delaboration that we want to keep. So, we can't do `attribute [coe] pure`. But,
  `norm_cast` doesn't accept adding lemmas that don'e have a `coe`-function, either.
  So, we need to manually add them to the simpExtension: see the #eval's below.
-/
#eval Lean.Meta.NormCast.addMove `ℝRange.neg_pure
#eval Lean.Meta.NormCast.addMove `ℝRange.pure_sub_pure
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
