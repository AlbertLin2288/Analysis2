import Analysis2.Structure.CommGroup
import Analysis2.Structure.CommSemiRing
noncomputable section
namespace my
open Classical
open Zero One
open Monoid CommMonoid CommGroup SemiRing CommSemiRing

class CommRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] [CommMonoid α] [CommGroup α] where
  _mul_one : ∀(a : α), a * one = a
  _mul_assoc : ∀(a b c : α), (a * b) * c = a * (b * c)
  _add_mul : ∀(a b c : α), (a + b) * c = a * c + b * c
  _zero_ne_one : (zero : α) ≠ one -- non-trvial
  _mul_comm : ∀(a b : α), a * b = b * a

namespace CommRing

  open Monoid CommGroup SemiRing
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [CommMonoid α] [CommGroup α] [CommRing α]

  private theorem _mul_zero : ∀ (a : α), a * zero = zero := by
    intro a
    rw [←add_right_inj_iff (c := a), add_zero]
    rw (occs := .pos [1]) [←_mul_one a]
    rw [_mul_comm, _mul_comm a, ←_add_mul, add_zero, _mul_comm, _mul_one]

  @[default_instance] instance : CommSemiRing α := ⟨_mul_one, _mul_assoc, _mul_zero, _add_mul, _zero_ne_one, _mul_comm⟩

  theorem mul_neg_left {a b : α} : (-a) * b = -(a * b) := by
    rw [←sum_zero_iff, ←add_mul, neg_add, zero_mul]

  theorem mul_neg_right {a b : α} : a * (-b) = -(a * b) := by
    rw [←sum_zero_iff, ←mul_add, neg_add, mul_zero]

  theorem mul_neg_both (a b : α) : (-a) * (-b) = a * b :=
   neg_neg (a*b) ▸ mul_neg_right (a:=a) ▸ mul_neg_left (a:=a) (b:=-b)

  theorem mul_sub : ∀(a b c : α), a * (b - c) = a * b - a * c := by
    intros;simp only [mul_add, mul_neg_right]

  theorem sub_mul : ∀(a b c : α), (a - b) * c = a * c - b * c := by
    intros;simp only [add_mul, mul_neg_left]

end CommRing



class CommRing' (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] [CommMonoid α] [CommGroup α] [CommRing α] where
  mul_eq_zero {a b : α} : a * b = zero → a = zero ∨ b = zero -- equivalent to mul_pos, see test2

namespace CommRing'
  open Monoid CommMonoid CommGroup SemiRing CommSemiRing CommRing
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [Inv α] [CommMonoid α] [CommGroup α] [CommRing α] [CommRing' α]

end CommRing'



end my
