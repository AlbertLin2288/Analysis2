import Analysis2.Structure.CommMonoid
noncomputable section
namespace my
open Classical
open Zero One
open Monoid CommMonoid


class SemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [CommMonoid α] where
  mul_one : ∀(a : α), a * one = a
  one_mul : ∀(a : α), one * a = a
  mul_assoc : ∀(a b c : α), (a * b) * c = a * (b * c)
  mul_zero : ∀(a : α), a * zero = zero
  zero_mul : ∀(a : α), zero * a = zero
  mul_add : ∀(a b c : α), a * (b + c) = a * b + a * c
  add_mul : ∀(a b c : α), (a + b) * c = a * c + b * c
  zero_ne_one : (zero : α) ≠ one -- non-trvial

namespace SemiRing

  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [CommMonoid α] [SemiRing α]

  instance : Std.Associative (α := α) Mul.mul := ⟨mul_assoc⟩

end SemiRing

end my
