import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.RCLike.Basic

theorem Real.min_natPow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    min x y ^ n = min (x ^ n) (y ^ n) := by
  rcases min_cases x y with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [h₁, left_eq_inf]
    exact pow_le_pow_left₀ hx h₂ n
  · rw [h₁, right_eq_inf]
    exact pow_le_pow_left₀ hy h₂.le n

theorem Real.max_natPow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    max x y ^ n = max (x ^ n) (y ^ n) := by
  rcases max_cases x y with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [h₁, left_eq_sup]
    exact pow_le_pow_left₀ hy h₂ n
  · rw [h₁, right_eq_sup]
    exact pow_le_pow_left₀ hx h₂.le n

--PR'ed, see #28416
instance
    {α : Type u_1} {β : Type u_2} [Preorder α] [Preorder β]
    [TopologicalSpace α] [TopologicalSpace β] [OrderTopology α] [OrderTopology β]
    : ContinuousMapClass (α ≃o β) α β where
  map_continuous := OrderIso.continuous

--See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/RingHom.20for.20not-a-ring/with/534826682
-- for discussion of this
section MinimalRing

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

end MinimalRing
