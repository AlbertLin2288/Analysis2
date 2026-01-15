import Analysis2.Structure.CommSemiRing
import Analysis2.CompStructure.OrderedSemiRing
noncomputable section
namespace my
open Classical
open Comp
open Zero One
open Monoid CommMonoid SemiRing CommSemiRing
open OrderedMonoid OrderedCommMonoid OrderedSemiRing


class OrderedCommSemiRing (α : Type) [Zero α] [Add α] [One α] [Mul α] [Comp α] [CommMonoid α] [CommSemiRing α] [OrderedCommMonoid α] where
  _mul_le_mul_of_nonneg_right {a b c : α} : a ≤ b → zero ≤ c → a * c ≤ b * c
  _zero_le_one : (zero : α) ≤ one -- WLOG


namespace OrderedCommSemiRing

  open CommSemiRing
  open OrderedMonoid OrderedCommMonoid OrderedSemiRing
  variable {α : Type} [Zero α] [Add α] [One α] [Mul α] [Comp α] [CommMonoid α] [CommSemiRing α] [OrderedCommMonoid α] [OrderedCommSemiRing α]

  theorem _mul_le_mul_of_nonneg_left {a b c : α} : a ≤ b → c ≥ zero → c * a ≤ c * b := by
    intro h h'
    simp only [mul_comm]
    exact _mul_le_mul_of_nonneg_right h h'

  @[default_instance] instance : OrderedSemiRing α := ⟨_mul_le_mul_of_nonneg_right, _mul_le_mul_of_nonneg_left, _zero_le_one⟩

end OrderedCommSemiRing



end my
