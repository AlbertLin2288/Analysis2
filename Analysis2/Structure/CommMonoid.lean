import Analysis2.Operator
import Analysis2.Structure.Monoid
noncomputable section
namespace my
open Classical
open Zero One
open Monoid


class CommMonoid (α : Type) [Zero α] [Add α] where
  _add_zero : ∀(a : α), a + zero = a
  _add_assoc : ∀(a b c : α), (a + b) + c = a + (b + c)
  add_comm : ∀(a b : α), a + b = b + a

namespace CommMonoid

  variable {α : Type} [Zero α] [Add α] [CommMonoid α]

  instance : Std.Commutative (α := α) Add.add := ⟨add_comm⟩

  theorem _zero_add : ∀(a : α), zero + a = a := by
    intro a;rw [add_comm, _add_zero]

  @[default_instance] instance : Monoid α := ⟨_add_zero, _zero_add, _add_assoc⟩

  theorem add_right_comm : ∀ (a b c : α), (a + b) + c = (a + c) + b := by
    intros
    ac_nf

  theorem add_left_comm : ∀ (a b c : α), a + (b + c) = b + (a + c) := by
    intros
    ac_nf

end CommMonoid

end my
