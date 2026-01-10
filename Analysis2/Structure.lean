import Analysis2.Operator
noncomputable section
namespace my
open Classical
open Zero One

-- variable (α : Type)

class Monoid (α : Type) [Zero α] [Add α] where
  add_zero : ∀(a : α), a + zero = a
  zero_add : ∀(a : α), zero + a = a
  add_assoc : ∀(a b c : α), (a + b) + c = a + (b + c)

namespace Monoid

  variable {α : Type} [Zero α] [Add α] [Monoid α]

  instance : Std.Associative (α := α) Add.add := ⟨add_assoc⟩

end Monoid

open Monoid



class CommMonoid (α : Type) [Zero α] [Add α] extends Monoid α where
  add_comm : ∀(a b : α), a + b = b + a

namespace CommMonoid

  variable {α : Type} [Zero α] [Add α] [CommMonoid α]

  instance : Std.Commutative (α := α) Add.add := ⟨add_comm⟩


  theorem add_right_comm : ∀ (a b c : α), (a + b) + c = (a + c) + b := by
    intros
    ac_nf

  theorem add_left_comm : ∀ (a b c : α), a + (b + c) = b + (a + c) := by
    intros
    ac_nf

end CommMonoid

open CommMonoid


class CommGroup (α : Type) [Zero α] [Add α] [Neg α] extends CommMonoid α where
  add_neg : ∀(a : α), a + (-a) = zero

namespace CommGroup

  variable {α : Type} [Zero α] [Add α] [Neg α] [CommGroup α]

  @[default_instance, reducible] instance : Sub α where
    sub := fun a b => a + (-b)

  theorem neg_add : ∀(a : α), (-a) + a = zero := by
    intro a
    rw [add_comm, add_neg]

  theorem neg_neg : ∀(a : α), - (-a) = a := by
    intro a
    rw [← add_zero (- -a), ← neg_add a, ← add_assoc, neg_add, zero_add]

  theorem neg_inj {a b : α} : -a = -b → a = b := by
    intro h
    rw [← neg_neg a, h, neg_neg]

  theorem neg_inj_iff {a b : α} : -a = -b ↔ a = b :=
    Iff.intro neg_inj (congrArg _)

end CommGroup



class SemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] extends CommMonoid α where
  -- one : α
  mul_one : ∀(a : α), a * one = a
  one_mul : ∀(a : α), one * a = a
  mul_assoc : ∀(a b c : α), (a * b) * c = a * (b * c)
  mul_zero : ∀(a : α), a * zero = zero
  zero_mul : ∀(a : α), zero * a = zero
  mul_add : ∀(a b c : α), a * (b + c) = a * b + a * c
  add_mul : ∀(a b c : α), (a + b) * c = a * c + b * c

namespace SemiRing

  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [SemiRing α]

  instance : Std.Associative (α := α) Mul.mul := ⟨mul_assoc⟩

end SemiRing

open SemiRing



class CommSemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] extends SemiRing α where
  mul_comm : ∀(a b : α), a * b = b * a

namespace CommSemiRing

  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [CommSemiRing α]

  instance : Std.Commutative (α := α) Mul.mul := ⟨mul_comm⟩

end CommSemiRing

open CommSemiRing

class CommRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] extends CommSemiRing α, CommGroup α

end my
