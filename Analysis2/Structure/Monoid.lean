import Analysis2.Operator
noncomputable section
namespace my
open Classical
open Zero One


class Monoid (α : Type) [Zero α] [Add α] where
  add_zero : ∀(a : α), a + zero = a
  zero_add : ∀(a : α), zero + a = a
  add_assoc : ∀(a b c : α), (a + b) + c = a + (b + c)

namespace Monoid

  variable {α : Type} [Zero α] [Add α] [Monoid α]

  instance : Std.Associative (α := α) Add.add := ⟨add_assoc⟩

end Monoid


end my
