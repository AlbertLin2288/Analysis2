import Analysis2.Structure
import Analysis2.Comp
noncomputable section
namespace my
open Classical
open Comp
open Zero One


class OrderedMonoid (α : Type) [Zero α] [Add α] extends Monoid α, Comp α where
  add_le_add_left {a b : α} : a ≤ b → ∀(c : α), c + a ≤ c + b
  add_le_add_right {a b : α} : a ≤ b → ∀(c : α), a + c ≤ b + c

namespace OrderedMonoid

  variable {α : Type} [Zero α] [Add α] [OrderedMonoid α]

end OrderedMonoid



class OrderedCommMonoid (α : Type) [Zero α] [Add α] extends CommMonoid α, OrderedMonoid α

namespace OrderedCommMonoid

  open OrderedMonoid
  variable {α : Type} [Zero α] [Add α] [OrderedCommMonoid α]

end OrderedCommMonoid



class OrderedCommGroup (α : Type) [Zero α] [Add α] [Neg α] extends CommGroup α, OrderedCommMonoid α
  -- add_neg : ∀(a : α), a + (-a) = zero

namespace OrderedCommGroup

  open OrderedMonoid OrderedCommMonoid
  variable {α : Type} [Zero α] [Add α] [Neg α] [OrderedCommGroup α]

end OrderedCommGroup



class OrderedSemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] extends SemiRing α, OrderedCommMonoid α where
  mul_nonneg {a b : α} : zero ≤ a → zero ≤ b → zero ≤ a * b

namespace OrderedSemiRing

  open OrderedMonoid OrderedCommMonoid
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [OrderedSemiRing α]

end OrderedSemiRing



class OrderedCommSemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] extends CommSemiRing α, OrderedSemiRing α
  -- mul_comm : ∀(a b : α), a * b = b * a

namespace OrderedCommSemiRing

  open OrderedMonoid OrderedCommMonoid OrderedSemiRing
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [OrderedCommSemiRing α]

end OrderedCommSemiRing



class OrderedCommRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [Neg α] extends CommRing α, OrderedCommSemiRing α, OrderedCommGroup α

namespace OrderedCommRing

  open OrderedMonoid OrderedCommMonoid OrderedSemiRing OrderedCommSemiRing OrderedCommGroup
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Neg α] [OrderedCommRing α]

end OrderedCommRing

end my
